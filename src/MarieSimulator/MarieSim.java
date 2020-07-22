// File:        MarieSim.java
// Author:      Julie Lobur
// JDK Version: 1.3.1, 5.0
// Date:        November 7, 2001, June 29, 2008, June 23, 2010
// Notice:      (c) 2003, 2008 Julia M. Lobur 
//              This code may be freely used for noncommercial purposes.
package MarieSimulator;
import java.io.*;
import java.util.*;
@SuppressWarnings("unchecked") // This line is needed because we are not using generics.

public class MarieSim {
/******************************************************************************************
*  This program simulates the operations that take place within a computer that uses a    *
*  "von Neumann" architecture.  This simulator is an implementation of the machine        *
*  described in *The Essentials of Computer Organization and Architecture* by Null and    *
*  Lobur.                                                                                 *
*                                                                                         *
*  Every reasonable effort has been made to give the user total control over the          *
*  operation and behavior of the simulator.  Programs can be written using the callable   *
*  editor, which also provides access to the MARIE assembler.  Once assembled, the user   *
*  can step through instructions one at a time, run a series of instructions to           *
*  breakpoints that he or she has set, or the program may be run to its programmed        *
*  termination.                                                                           *
*                                                                                         *
*  Overall control of the simulator is determined by the state of the machine, kept in    *
*  the instance variable machineState, the values of which are given below.  The state    *
*  of the machine determines what operations are allowable and which step can be taken    *
*  next.                                                                                  *
******************************************************************************************/
/* --                                                                                 -- */
/* --  Class fields and attributes.                                                   -- */
/* --                                                                                 -- */
  public static String         mexFile = null;     // Name of machine code file.
  public static String         mexPath = null;
  public static final String  MEX_TYPE = ".mex";  // File extension of executable code.
  public static final String  MAP_TYPE = ".map";  // File extension of symbol table.
  public static final String  SRC_TYPE = ".mas";  // File extension for source code.
  public static final String  DMP_TYPE = ".dmp";  // File extension for core dump.

  public static final String      linefeed = System.getProperty("line.separator");
  public static final String      formfeed = "\014";
  public static final String fileSeparator = System.getProperty("file.separator");

  public static final String HELP_FILE = "msimhlp1.txt";  // Help file name.
                                 
  public static final String[] errorMsgs = {
                                         "Program terminated normally.",       //  0
                                         "Illegal opcode",                     //  1
                                         "Illegal conditional operand",        //  2
                                         "Address out of range",               //  3
                                         "Invalid machine code format",        //  4
                                         "IO Exception on input file",         //  5
                                         "Invalid register",                   //  6
                                         "Illegal numeric value in register",  //  7
                                         "Maximum program statements reached"  //  8
                                         };
/* --                                                                                 -- */
/* --  boolean array operandReqd indicates whether an instruction with hexcode        -- */
/* --  corresponding to the position in the array requires an operand.                -- */
/* --  The fetch() operation needs to know this.                                      -- */
/* --                                                                                 -- */
  public static final boolean[] operandReqd = { true,   // JUMPNSTORE
                                                true,   // LOAD
                                                true,   // STORE
                                                true,   // ADD
                                                true,   // SUBT
                                                false,  // INPUT
                                                false,  // OUTPUT
                                                false,  // HALT
                                                false,  // SKIPCOND
                                                false,  // JUMP
                                                false,  // CLEAR
                                                true,   // ADDI
                                                true,   // JUMPI
                                                true,   // LOADI
                                                true }; // STOREI
/* --                                                                                 -- */
/* --  System constants.                                                              -- */
/* --                                                                                 -- */
  public static final int MAX_MARIE_INT   =  32767;
  public static final int MIN_MARIE_INT   = -32768;
  public static final int MAX_MARIE_ADDR  =   4095;
  public static final int HEX             =      0;      // Register display modes,
  public static final int DEC             =      1;      // i.e., "rendering modes."
  public static final int ASCII           =      2;

  public static final int MARIE_HALTED_NORMAL     =  0;  // Possible machine states.
  public static final int MARIE_RUNNING           =  1;
  public static final int MARIE_BLOCKED_ON_INPUT  =  2;
  public static final int MARIE_PAUSED            =  3;
  public static final int MARIE_HALTED_ABNORMAL   = -1;
  public static final int MARIE_HALTED_BY_USER    = -2;
  public static final int MARIE_NO_PROGRAM_LOADED = -3;
  public static final int MARIE_UNINITIALIZED     = 0xDEAD;

  public static final int AC     = 0;                    // Register numbers used for
  public static final int IR     = 1;                    // designations in inner class
  public static final int MAR    = 2;                    // Register for error-checking.
  public static final int MBR    = 3;
  public static final int PC     = 4;
  public static final int INPUT  = 5;
  public static final int OUTPUT = 6;

  static final int MEMORY_TABLE_ROW_HEIGHT = 15;  // Make sure the address and code table
                                                  // rows are the same height.
  static final int PROGRAM_TABLE_ROW_HEIGHT = 19; // Give us a bit larger row for 
                                                  // the program instructions.

  public static final int MINIMUM_DELAY = 10;
  public static final String[] base = {"Hex", "Dec", "ASCII"};
  public static final String[] outputControl = {"Control", "Use Linefeeds", "No Linefeeds", 
                                                "Clear output", "Print"};
/* --                                                                                 -- */
/* --  Instance variables.                                                            -- */
/* --                                                                                 -- */
  Scanner scanner = new Scanner(System.in);
  int  instructionCode = 0;            // Machine code of instruction being run.
  int    codeLineCount = 0;            // Number of lines in the program
  boolean     stepping = false;        // Whether executing one instruction at a time.
  boolean breakpointOn = false;        // Whether executing to a breakpoint.
  int            delay = 10;           // Delay between instruction executions;
  boolean outputWithLinefeed = true;   // Determines whether characters output will have 
                                       // linefeeds supplied.  User can change this.
  static  String  statusMessage = null;
  static  Vector   outputStream = new Vector();  // Holds output so we can reformat.
  int              machineState = 0xDEAD;        // Machine state.

  boolean errorFound = false;   // Non-fatal error flag, e.g. invalid  user input.
  boolean fatalError = false;   // Fatal error flag, e.g., invalid branch address.
  int      errorCode = 0;

  Object[][] programArray;                // Holds instructions to be executed.
  ProgramTableModel    ptm = new ProgramTableModel();  // Program monitor table control.
  int      programFocusRow = 0;           // Current instruction pointer in monitor.
  Hashtable codeReference                 // codeReference provides correspondence
            = new Hashtable(16, (float) 0.75);   // between monitor table and 
                                          // instruction addresses.
                                          // Initial capacity 16, load factor 0.75.

  Register         regAC = new Register(AC);        // its label, and the combo box used to
                                                    // one for each register except the
  Register         regIR = new Register(IR);

  Register        regMAR = new Register(MAR);

  Register        regMBR = new Register(MBR);

  Register         regPC = new Register(PC);

  Register      regINPUT = new Register(INPUT);

  Register           regOUTPUT = new Register(OUTPUT);

  Object[][] memoryArray = new Object[256][17]; // Memory contents.
  int    memoryFocusCell = 0;                   // Current memory location in table.
     
                                             //    message window. 

  class ProgramTableModel {
/******************************************************************************************
*  This class provides the framework for the table used for the program statement         *
*  execution monitor window.  We have to make it global to the simulator because we       *
*  change the structure of the table (i.e., the number of rows) each time a different     *
*  program is loaded from disk.)                                                          *
******************************************************************************************/
      String headers[] =  { " ", " ", "label", "opcode", "operand", "hex"};
      public int getColumnCount() { return headers.length; }
      public int getRowCount() { return codeLineCount; }
      public String getColumnName(int col) {
        return headers[col]; }
      public Object getValueAt(int row, int col) {
        return programArray[row][col];
      }
  
      public boolean isCellEditable(int rowIndex, int columnIndex) {
        if (columnIndex == 0 )                // Determines whether the data
          return true;                        // value in a cell can be changed.
        else
          return false;
      }
      public void setValueAt(Object value, int row, int col) {
        programArray[row][col] = value;       // Only one column is editable,
      }
      public Class getColumnClass(int c) {    // This method is used to provide 
        return getValueAt(0, c).getClass();   // the default cell editor.  I.e.,
      }                                       // Booleans display as checkboxes.
    } // ProgramTableModel

  class Register {
/******************************************************************************************
*   MARIE registers have two principal characteristics:  their value and their rendering  *
*   mode, which is the radix system that is used to express their value.  For any         *
*   register instance, the user can change modes using the combobox on the register       *
*   display.                                                                              *
*                                                                                         *
*   Registers are designated by MARIE class constants, e.g., AC = 0, to allow us control  *
*   over which values are valid for the register.  Specifically, a memory address can     *
*   have a value of only FFF hex while the accumulator can use the entire machine word    *
*   size (up to FFFF).  We use bitwise operations to prevent unreasonable values from     *
*   causing problems.  This is mimics register overflow situations on real systems.       *
*                                                                                         *
*   Each register instance has a text rendering which is a function of both its value     *
*   and its mode.  So decimal value 65 would be "41" in hex mode and "A" in ASCII mode.   *
*   The rendering is also padded with blanks and zeroes to provide an orderly and         *
*   accurate display in the TextField.                                                    *
******************************************************************************************/
    int    designation; // Register number.
    short  value;       // value stored.
    int    mode;        // HEX, DEC, or ASCII.
    String rendering;   // String of value in mode: e.g., value = 12 = "C".

    public Register(int whichOne) {      // Constructor.
      if ((whichOne >= AC) && (whichOne <= OUTPUT))     // Make sure we have a valid 
        designation = whichOne;                         // designation.
      else {
        fatalError = true;
        errorCode = 6;
      }
      setValue(0);                                      // Initialize its value and
      mode = HEX;                                       // default the mode to hex.
    } // Register()

    public void setMode(int m) {
/******************************************************************************************
*   Set Register display mode, which defaults to hex.  The rendering (i.e., character     *
*   display mode) of the register is changed to reflect the mode of the register.  So     *
*   if the register contains decimal 15, its rendering in decimal is "15."  When the      *
*   mode is changed to hex, the rendering changes to "000F."                              *
******************************************************************************************/
      if ((m == DEC) || (m == ASCII)) 
        mode = m;
      else
        mode = HEX;
      setValue(value);
    } // setMode()

    public void setValue(int v) {
/******************************************************************************************
*   Sets the numeric value stored in the Register to the integer argument value.  The     *
*   argument is always a base 10 integer.  Hence, if the register is in hex mode and a    *
*   decimal 15 is passed in the argument, decimal 15 is stored in the value field and     *
*   "000F" is stored in the rendering field.                                              *
******************************************************************************************/
      value = (short) v;
      if ((this.designation == MAR)            // Wrap memory addresses that are
           ||(this.designation == PC))   {     // out of range.
         if ((value < 0) || (value > MAX_MARIE_ADDR))
           value = (short) (v & 0x00000FFF);
      }
      switch (mode) {
        case   HEX: if ((designation == MAR) 
                             ||(designation == PC))  
                      rendering = "  "+to3CharHexStr(value);
                    else
                      rendering = " "+to4CharHexStr(value);
                    break;
        case ASCII: if (v == 0)
                      rendering = null;
                    else
                      rendering = "    " + (char) (v % 128);
                    break;
           default: 
                    if ((designation != OUTPUT) && (value > 0))
                      rendering = " "+Integer.toString(value); 
                    else
                      rendering = Integer.toString(value); 
      } // switch
    } // setValue ()
  
    public void setValue(String v) {
/******************************************************************************************
*   Sets the value in the register to the numeric value passed in the String argument     *
*   v.  This value is interpreted according to the current mode of the register.  So      *
*   if the register is in decimal mode, the string will be parsed consistent with the     *
*   mode. For example, if the register is in decimal mode, the string "15" is             *
*   interpreted as decimal 15.  If the register is in hex mode, the string "15" is        *
*   interpreted as decimal 21.                                                            *
******************************************************************************************/
        value = (short) stringToInt(mode, v);
        if (!errorFound)  {                          // If the string converted ok,
          setValue(value);                           // put it in the register.
        }
        else {                                       // Did not convert okay.
          fatalError = true;                         // Fatal error.
          errorCode = 7;
        }
    } // setValue()

    public String toString() { return rendering; }  // Accessor for value in string form.

    public int getValue() {                         // Accessor for value in integer form.
       if ((this.designation == MAR)                // If we have an address-type register,
             ||(this.designation == PC)) {          // always return a positive value.
         if (this.value < 0) {
           int v = value;
           value = (short) (v & 0x00000FFF);
         }
       }
    return value; 
    }
  } // Register


  public MarieSim() {
/******************************************************************************************
*  This is the constructor for the simulator.                                             *
******************************************************************************************/
           stepping = false;
           clearBreakPoints();

/* --                                                                                 -- */
/* -- Accumulator                                                                     -- */
/* --                                                                                 -- */
    regAC.setValue(0);
/* --                                                                                 -- */
/* -- Instruction Register (IR)                                                       -- */
/* --                                                                                 -- */
    regIR.setValue(0);
/* --                                                                                 -- */
/* -- Memory Address Register (MAR)                                                   -- */
/* --                                                                                 -- */
    regMAR.setValue(0);
/* --                                                                                 -- */
/* -- Memory Buffer Register (MBR)                                                    -- */
/* --                                                                                 -- */
    regMBR.setValue(0);
/* --                                                                                 -- */
/* -- Program Counter (PC)                                                            -- */
/* --                                                                                 -- */
    regPC.setValue(0);
/* --                                                                                 -- */
/* -- Input Register (INPUT)                                                          -- */
/* --                                                                                 -- */
    regINPUT.setValue(0);
    regINPUT.setMode(DEC);
/* --                                                                                 -- */
/* -- Output register (OUTPUT)                                              -- */
/* --                                                                                 -- */
    regOUTPUT.setValue(0);
    regOUTPUT.setMode(DEC);
    outputWithLinefeed = true;
  } // MarieSim()

/* --  Marie machine functional methods --------------------------------------------- -- */
/* --                                                                                 -- */
/* --  Manipulators and converters for hex, decimal and ASCII values.                 -- */
/* --                                                                                 -- */
  int stringToInt(int mode, String literal) {
/******************************************************************************************
* Converts a String to an integer value.                                                  *
* Parameters:                                                                             *
*     int mode = DEC, HEX or ASCII (final static int constants),                          *
*     the String literal to be converted to an integer.                                   *
* As with actual hardware registers, this method returns a value only up to the word size *
* of the system.  So to return a value that can be stored in a 16-bit register, we use    *
* an intermediate short integer.                                                          *
* This method will return Integer.MAX_VALUE to flag any exceptions thrown.  (We can get   *
* away with this because Marie's word size is smaller than Java's.) The errorFound flag   *
* is also set.  The invoking method can decide what to do about it.                       *
******************************************************************************************/
    errorFound = false;
    String numStr = literal.trim();
    short shortResult = 0;
    int result = Integer.MAX_VALUE;

    switch (mode) {
      case (DEC): {      // DECimal literal.
                 try {
                   shortResult = (short) Integer.parseInt(numStr, 10);
                 }
                 catch (NumberFormatException e) {
                   errorFound = true;
                   return result;
                 }
                 break;
               }

      case (HEX): {    // HEXadecimal literal.
                 try {
                   shortResult = (short) Integer.parseInt(numStr, 16);
                 }
                 catch (NumberFormatException e) {
                   errorFound = true;
                   return result;
                 }
                 break;
               }
      case (ASCII):   // Return value of first ASCII character of a string.
                  if (numStr.length() == 0)     // Return zero on a null string.
                    return 0;
                  int i = (int) numStr.charAt(0);
                  return i % 128;
      } // switch()
    result = shortResult;
    return result;
  } // stringToInt()

  String to3CharHexStr(int number) {
/******************************************************************************************
* Converts the argument number to a string containing exactly 3 characters by padding     *
* shorter strings and truncating longer strings.  So an argument larger than 8092 or      *
* smaller than 0 will be truncated to end up in the (unsigned) range 0 - 4095.            *
******************************************************************************************/
                                              // If number negative, convert to 16-bit 2's
    if (number < 0) {                         // complement by shifting the low-order 20
      number = number << 20;                  // bits to the high-order bits.  (We lose the
    }                                         // rightmost bits below.)

    String    hexStr = Integer.toHexString(number).toUpperCase();
    switch (hexStr.length()) {
       case 1: hexStr = "00"+hexStr;                 // Pad strings shorter than 3 chars.
               break;
       case 2: hexStr = "0" +hexStr;
               break;
       case 3: break;
      default: hexStr =  hexStr.substring(0, 3);     // Truncate strings longer than 3 chars
    } // switch()
    return hexStr;
  } // to3CharHexStr()

  String to4CharHexStr(int number) {
/******************************************************************************************
* Same as above (to3CharHexStr()), only returns a string of exactly 4-characters that are *
* in the (decimal) range -32,768 to 32,767.                                               *
******************************************************************************************/
    if (number < 0) {                           // If number negative, convert to 16-bit 2's
      number = number << 16;                    // complement by shifting the low-order 16
    }                                           // bits to the high-order bits.  (We lose the
                                                // rightmost 16 bits below.)
    String    hexStr = Integer.toHexString(number).toUpperCase();
    switch (hexStr.length()) {
       case 1: hexStr =  "000" + hexStr;             // Pad strings shorter than 4 chars.
               break;
       case 2: hexStr =  "00"  + hexStr;
               break;
       case 3: hexStr =  "0"   + hexStr;
               break;
       case 4: break;
      default: return hexStr.substring(0, 4);   // Truncate strings longer than 4 chars.
    } // switch()
    return hexStr;
  } // to4CharHexStr()


  String rightJustifyIn4 (String s) {
/******************************************************************************************
*  Right-justifies the argument string into a four-character cell, padding out with       *
*  leading blanks.  If string is longer than 4 chars, only its rightmost 4 chars          *
*  are taken.                                                                             *
******************************************************************************************/
    StringBuffer justified = new StringBuffer("    ");
    int len = s.length(),
          j = 3;
    for (int i = len-1; ((i >=0) && (j >=0)) ; i--) {
       justified.setCharAt((j--),s.charAt((i)));
    }
    return justified.toString();
  } // rightJustifyIn4()


/* ------------------------------------------------------------------------------------- */
/* -- General output methods.                                                         -- */
/* ------------------------------------------------------------------------------------- */
  void setStatusMessage(String msg) {
/******************************************************************************************
*  Writes the message, msg, to the standard output                                        *
******************************************************************************************/
   System.out.println(msg);
  } // setErrorMessage()


/* ------------------------------------------------------------------------------------- */
/* -- Machine loading and reset methods.                                              -- */
/* ------------------------------------------------------------------------------------- */
  void getProgram(String aFileName) {
/******************************************************************************************
*  This method accepts a filename and path from a JFileChooser dialog.  The path and      *
*  file extension are stripped off so the root filename can be used to locate other       *
*  files related to the executable, such as the symbol table.  The pathname is also       *
*  retained so that it can be passed to the editor if the user wishes to edit the         *
*  program source code.  When all of this parsing is completed, the loadProgram()         *
*  method is invoked.                                                                     *
******************************************************************************************/
    int dirEndPos = 0;                                 // Strip the path to
    int extensionStart = 0;                            // get the filePrefix.
    dirEndPos = aFileName.lastIndexOf(fileSeparator);
    if (dirEndPos < 0) {
     dirEndPos = -1;
     mexPath = ".";
    }
    else
      mexPath = aFileName.substring(0, dirEndPos);     // Save the path.
    extensionStart = aFileName.lastIndexOf(MEX_TYPE);   
    if (extensionStart > 0)                            // Save the root filename.
      mexFile = mexPath + fileSeparator + aFileName.substring(dirEndPos+1, extensionStart);
    loadProgram();                                     // Get the program.
  } // getProgram()


  void loadProgram() {
/******************************************************************************************
*  This method does the work of loading an ObjectStream of executable AssembledCodeLines  *
*  from disk.  This method should be called only by methods that have already established *
*  a valid filename.  We check to make sure that this filename isn't null before trying   *
*  to find the file.                                                                      *
*                                                                                         *
*  If we don't find the file, or if it's corrupted, the Exception caught is sent to the   *
*  message area of the simulator.                                                         *
*                                                                                         *
*  If we have found a valid file, the first thing we do is clear any remnants from a      *
*  previously-loaded program.  Then we load the codelines into a Vector from which        *
*  an enumeration will be used to load the program instruction array (programArray)       *
*  and the memoryArray.  We load into a Vector prior to loading the data structures       *
*  so that we can find out how big to make the programArray.  (This is created new        *
*  for each program loaded.)                                                              *
*                                                                                         *
*  Program line numbers are loaded into a HashTable that provides a correspondence        *
*  between the memory address of the program statement and the location of that           *
*  statement in the program monitor table.  We retrieve these addresses during the        *
*  fetch cycle.                                                                           *
*                                                                                         *
*  After all of the data structures are loaded, we set the menu options and menu          *
*  buttons appropriately.  If a symbol table for the loaded program can be found, the     *
*  menu option for displaying this table is also enabled.  If all loading was successful, *
*  the machineState will be HALTED_NORMAL.  If there was a fatal error encountered        *
*  during the load, the machineState will be NO_PROGRAM_LOADED after the marieReset()     *
*  call is performed.                                                                     *
******************************************************************************************/
    File               objectFile = null; 
    ObjectInputStream   objFileIn = null;
    AssembledCodeLine   aCodeLine = new AssembledCodeLine();
    Vector             codeVector = new Vector();
    errorFound = false;
    if (mexFile == null) {
      setStatusMessage(" No file to load.");
      return;
    }
    try {                                      // Try to open the input.
      objectFile = new File(mexFile+MEX_TYPE);
      objFileIn = new ObjectInputStream( new FileInputStream(objectFile) );
    } // try
    catch (FileNotFoundException e) {
      setStatusMessage(" File " + mexFile + MEX_TYPE + " not found.");
      errorFound = true;
    } // catch
    catch (IOException e) {
      setStatusMessage(" "+e); 
      errorFound = true;
    } // catch
    catch (Exception e) {
      setStatusMessage(" "+e); 
      errorFound = true;
    } // catch
    if (errorFound)                            // If we've found any problems,
      return;                                  // return to caller.
    marieReset();                              // Clear the simulator, including
    if (codeLineCount >=0)                     // any program loaded.         
      for (int i = 0; i < codeLineCount; i++) {
        programArray[i][0] = new Boolean(false);
        programArray[i][1] = "  ";
        programArray[i][2] = "  ";
        programArray[i][3] = "  ";
        programArray[i][4] = "  ";
        programArray[i][5] = "  "; 
      }
    codeLineCount = 0;
    boolean done = false;                      // Begin loading the program...
    while (!done) {
       if (codeLineCount >= MAX_MARIE_ADDR) {
         setStatusMessage(" Maximum program statements reached."); 
         errorFound = true;
         done = true;
       } // if
       try {             
          aCodeLine = (AssembledCodeLine) objFileIn.readObject();
          if (aCodeLine == null)
             done = true;
          else { 
            if (aCodeLine.lineNo.charAt(0) != ' ') {
              codeVector.add(aCodeLine);
              codeLineCount++;
            } // if
          } // else
       } // try
       catch (EOFException e) {                // At EOF, we're done.  
         done = true;                          // Other exceptions are "fatal."
       } // catch
       catch (IOException e) {
         setStatusMessage(" "+e);  
         errorFound = true;
         done = true;
       } // catch
      catch (Exception e) {
        setStatusMessage(" "+e); 
        errorFound = true;
        done = true;
      } // catch
      if (done)
        break;
    } // while
    try {                                      // Close the input.
       objFileIn.close(); 
       objectFile = null;
    } // try
    catch (IOException e) {
       setStatusMessage(" "+e); 
    } // catch
    if (errorFound)                            // If we found serious errors, return
      return;                                  // to caller.
    int addr = 0;
    programArray  = new Object[codeLineCount][6];    // Prepare program-specific data 
    codeReference.clear();                           // structures.
    Enumeration e = codeVector.elements();
    int lineCount = 0;

    while (e.hasMoreElements()) {                    // Load data structures.
      aCodeLine = (AssembledCodeLine) e.nextElement();
      programArray[lineCount][0] = new Boolean(false);      // Load the monitor table...
      programArray[lineCount][1] = "  "+aCodeLine.lineNo;
      programArray[lineCount][2] = " "+aCodeLine.stmtLabel;
      programArray[lineCount][3] = aCodeLine.mnemonic;
      programArray[lineCount][4] = aCodeLine.operandToken;
      programArray[lineCount][5] = " "+aCodeLine.hexCode+aCodeLine.operand; 
      codeReference.put(aCodeLine.lineNo, new Integer(lineCount));
      lineCount++;
      try {
        addr = Integer.parseInt(aCodeLine.lineNo, 16);      // ... and load memory.
      }
      catch (NumberFormatException exception) {
        continue;
      } // catch
        memoryArray[addr / 16][addr % 16 + 1] = " "+aCodeLine.hexCode+aCodeLine.operand;
    } // while();
    String aString = (String) programArray[0][1];
    try {                                                  // Get memory cell of
          addr = Integer.parseInt(aString.trim(), 16);     // first instruction.
    }                                               
    catch (NumberFormatException exception) {
           ;
    } // catch
    regPC.setValue(addr);                                  // Set PC to first address
    breakpointOn = false;
    checkForMap();
    if (stepping)
       ;
    machineState = MARIE_HALTED_NORMAL;
  } // loadProgram()


  void checkForMap() {
/******************************************************************************************
*   Checks to see whether there is a symbol table on disk that goes with the program      *
*   that has been loaded.  If we find one, we activate the [Show Symbol Table] button.    *
******************************************************************************************/
    try { // Prove the previous statement true or false...                       
          InputStream fileIn = new FileInputStream(mexFile+MAP_TYPE);
        }
    catch (IOException e) {                       // No listing file available!
        }
  } // checkForMap()


  void restart() {
/******************************************************************************************
*   If the system is initialized and a program is loaded, this method resets the display  *
*   and program counter to their states after the program was initially loaded.  We       *
*   preserve user settings (e.g., "step mode") as they have been set by the user.         *
******************************************************************************************/
     if ((machineState == MARIE_UNINITIALIZED) ||
          (machineState == MARIE_NO_PROGRAM_LOADED))
        return;
     fatalError = false;
     errorCode = 0;
     if (stepping) {
       setStatusMessage(" Press [Step] to start.");
     }
     else {
        setStatusMessage("  Press [Run] to start.");
     }   
     regPC.setValue(((String) programArray[0][1]).trim()); // Set PC to first address of program loaded.
     programFocusRow = 0;
     machineState = MARIE_RUNNING;
  } // restart()


  void marieReset() {
/******************************************************************************************
*  This method has the effect of pressing the reset button on a physical machine: It      *
*  clears everything.                                                                     *
******************************************************************************************/
    regAC.setValue(0);                          // Reset all registers to 0.
    regIR.setValue(0);
    regMAR.setValue(0);
    regMBR.setValue(0);
    regPC.setValue(0);
    regINPUT.setValue(0);
    regOUTPUT.setValue(0);
    outputStream = new Vector();               // output Vector.
    for (int i = 0; i < 4095; i+= 16)  {       // Initialize memory.
      Arrays.fill(memoryArray[i / 16], " 0000");
      memoryArray[i / 16][0] = "  "+to3CharHexStr(i);
    }
    if (codeLineCount >=0)                     // If we already loaded a program, clear it.
      for (int i = 0; i < codeLineCount; i++) {
        programArray[i][0] = new Boolean(false);
        programArray[i][1] = "  ";
        programArray[i][2] = "  ";
        programArray[i][3] = "  ";
        programArray[i][4] = "  ";
        programArray[i][5] = "  "; 
      }
    programFocusRow = 0;
    memoryFocusCell = 0;
    machineState = MARIE_NO_PROGRAM_LOADED;
    breakpointOn = false;
  } // marieReset

/* --                                                                                 -- */
/* --  Marie operational methods.   (MARIE Microcode.)                                -- */
/* --                                                                                 -- */
  void fetchNext() {
/******************************************************************************************
*   This method performs the "fetch" part of the "fetch-execute" cycle.                   *
*                                                                                         *
*      Side effects: IR contains instruction,                                             *
*                    MAR contains operand address (if any)                                *
*                    MBR contains operand (if any)                                        *
*                    fatalError set if invalid opcode in instruction                      *
*                                     or invalid operand address.                         *
*                    Machine state set to MARIE_RUNNING.                                  *
******************************************************************************************/
    String aString;                  // These local variables make the code
    int  memoryRow, memoryCol;       // cleaner and easier to read.
    if (fatalError)  {                           // Stop if there has been an error.
      halt();
      return;
    }
    regMAR.setValue(regPC.getValue());           // Set MAR to address of next instruction.
    int addr = regMAR.getValue();                // seen on the screen, but we do it this
    memoryRow = addr / 16;                       // way because it's how the fetch-execute
    memoryCol = addr % 16 + 1;                   // process works.
    try {                                                             // Pull instruction
      regIR.setValue((" "+(String) memoryArray[memoryRow][memoryCol]).trim()); // from memory 
    }
    catch (ArrayIndexOutOfBoundsException e) {
             errorCode = 3;
             fatalError = true;
             return;
    } // catch
    aString = regPC.toString().trim();           // Move the cursor.
    if (codeReference.containsKey(aString)) {
      programFocusRow =((Integer) codeReference.get(aString)).intValue();
    }
    aString = regIR.toString().trim();
    try {
       instructionCode = Integer.parseInt(aString.substring(0,1), 16);
       if (instructionCode >= operandReqd.length)  // Make sure we have a valid hexcode.
         throw new NumberFormatException();        // This double-checks the operandReqd
    }                                              // array as well!
    catch (NumberFormatException e) {
      fatalError = true;
      errorCode = 1;
      return;
    }
    if (operandReqd[instructionCode]) {            // If instruction needs one,
      regMAR.setValue(regIR.toString().trim().substring(1,4));  // load the operand into MBR
      addr = regMAR.getValue();
      memoryRow = addr / 16;
      memoryCol = addr % 16 + 1;
      memoryFocusCell = addr;
      try {
        regMBR.setValue((" "+memoryArray[memoryRow][memoryCol]).trim()); 
        if (fatalError)
          return; 
      }
      catch (ArrayIndexOutOfBoundsException e) {
             errorCode = 3;
             fatalError = true;
             return;
      } // catch
    } // if operand
    regPC.setValue(regPC.getValue()+1);            // Increment PC.
    if (regPC.getValue() > MAX_MARIE_ADDR) {
       errorCode = 8;
       fatalError = true;
    }
    if (fatalError)
      return; 
    errorFound = false;                            // Reset error flag.
    machineState = MARIE_RUNNING;
  } // fetchNext()

  void execute () {
/******************************************************************************************
*   This method is the mainline of the "execute" part of the "fetch-execute" cycle.       *
******************************************************************************************/
    switch (instructionCode) {
       case  0: jnS();
                break;
       case  1: load();
                break;
       case  2: store();
                break;
       case  3: add();
                break;
       case  4: subt();
                break;
       case  5: input();
                break;
       case  6: output();
                break;
       case  7: halt();
                break;
       case  8: skipCond();
                break;
       case  9: jump();
                break;
       case 10: clear();
                break;
       case 11: addI();
                break;
       case 12: jumpI();
                break;
       case 13: loadI();
                break;
       case 14: storeI();
                break;         
      default:
        fatalError = true;
        errorCode = 1;
    } // switch
  } // execute()


  void jnS() { 
/******************************************************************************************
*   Jump and Store: Store PC at address [MAR] and set PC (jump) to address [MAR]+1.       *
*   (This instruction can be used to create subroutines in MARIE assembly language.)      *
******************************************************************************************/
     int memoryRow, memoryCol, addr;
     
     regMBR.setValue(regPC.getValue());
     addr = regIR.getValue();
     addr = addr & 0x0FFF;        // Strip the opcode from the instruction,
     regMAR.setValue(addr);       // leaving the address.
     
     memoryRow = addr / 16;
     memoryCol = addr % 16 + 1;
     try {
       memoryArray[memoryRow][memoryCol] = " "+to4CharHexStr(regMBR.getValue());
       regMBR.setValue(regMAR.getValue());
       regAC.setValue(regMBR.getValue()+1);
       regPC.setValue(regAC.getValue());
     }
     catch (ArrayIndexOutOfBoundsException e) {
             errorCode = 3;
             fatalError = true;
     }
   } // jnS() 

 
  void load() { 
/******************************************************************************************
*   Copies the operand from the MBR to the AC.  (The MBR is loaded during                 *
*   instruction fetch.)                                                                   *
******************************************************************************************/
     regAC.setValue(regMBR.getValue());
   } // load()


  void store() {
/******************************************************************************************
*   Store whatever is in the accumulator to the address specified in the MAR              *
*   by first moving it to the MBR.                                                        *
******************************************************************************************/
     int memoryRow, memoryCol;
     regMBR.setValue(regAC.getValue());
     if (fatalError)
       return; 
     int addr = regMAR.getValue();
     memoryRow = addr / 16;
     memoryCol = addr % 16 + 1;
     try {
       memoryArray[memoryRow][memoryCol] = " "+to4CharHexStr(regMBR.getValue());
     }
     catch (ArrayIndexOutOfBoundsException e) {
             errorCode = 3;
             fatalError = true;
     }
   } // store()


  void add() { 
/******************************************************************************************
*   Adds the value in the MBR to the AC.  (The MBR is loaded during instruction fetch.)   *
******************************************************************************************/
     regAC.setValue(regAC.getValue() + regMBR.getValue());
   } // add() 


  void subt() { 
/******************************************************************************************
*   Subtracts the value in the MBR from the AC.                                           *
******************************************************************************************/
     regAC.setValue(regAC.getValue() - regMBR.getValue());
   } // subt() 


  void input() { 
/******************************************************************************************
*   This method is called twice to effect one input.  The first time through, the         *
*   machine state is set to BLOCKED_ON_INPUT and the input register is enabled.  The      *
*   second time through, the input is moved to the accumulator and the register is        *
*   closed to additional input.  The second entry into this method is triggered by        *
*   an action event on the INPUT register.                                                *
*                                                                                         *
*   After the second pass, we need to resume processing after the blocking call.  If      *
*   the machineState is MARIE_RUNNING, we just call the runProgram() method again         *
*   because it terminated when the input() instruction was encountered.  If the           *
*   simulator is being run in "step" mode, we send a completion message and return        *
*   to the caller.                                                                        *
******************************************************************************************/
       regINPUT.setValue(scanner.nextInt());
       if (fatalError) {
         halt();
         return;
       } 
       regAC.setValue(regINPUT.getValue());
       if (fatalError) {
         halt();
         return;
       } 
       machineState = MARIE_RUNNING;             // Reset the machine state.
       if (stepping)                             // Proceed with next instruction
         ;        // or step.
       else {
         if (breakpointOn)
           runToBreakpoint();
         else  
           runProgram();
       }
   } // input()


  void output() { 
/******************************************************************************************
*   Copies the value in the AC to the output register and concatenates the value to       *
*   the text output vector.  Note:  The output appearance is controlled by the radix      *
*   mode of the output register.                                                          *
******************************************************************************************/
     regOUTPUT.setValue(regAC.getValue());
     String outStr = regOUTPUT.toString().trim(); // Put the OUT reg into a string so 
						  // we can manipulate it.
     if (outStr.length() == 0)                    // If the value is a whitespace,
       outStr = regOUTPUT.toString().substring(4, 5); // keep the whitespace char.
                                                  // Otherwise we lose our spaces!
     System.out.println(new Integer(regOUTPUT.getValue()));
     if (regOUTPUT.toString() != null) 
       ;
     if (outputWithLinefeed)
       ;
     else
       if ((regOUTPUT.getValue() == 13) && (regOUTPUT.mode == ASCII))
          ;
   } // output() 


  void halt() { 
/******************************************************************************************
*   Changes the machine state from (probably) RUNNING to HALTED using the fatalError      *
*   boolean to determine which one is which.  The statusMessage is also loaded with       *
*   a string from the errorMessage array so that it can be displayed.                     *
******************************************************************************************/
    stepping = false;
          
    if (fatalError) {
       machineState = MARIE_HALTED_ABNORMAL;
       if (errorCode < errorMsgs.length)
         setStatusMessage(" Machine halted abnormally.  Error: "+errorMsgs[errorCode]);
       else
         setStatusMessage(" Machine halted abnormally.");
    }
    else {
       machineState = MARIE_HALTED_NORMAL;
    }
   } // halt()

  void skipCond() { 
/******************************************************************************************
*   This instruction will skip over the instruction at PC+1 based on the value in the     *
*   instruction's lower 12 bits.                                                          *
******************************************************************************************/
     int cond = regIR.getValue();
     cond = cond & 0x0C00;   // Strip the opcode from the instruction.
     cond = cond >> 10;      // Shift the conditional to the low-order bits.
     if (cond == 3) {        // Check valid values for condition 0, 1, & 2.
      fatalError = true;
      errorCode = 2;
      return;
     }
     int accumulator = regAC.getValue();
     if (((accumulator < 0) && (cond == 0))        // Skip if accumulator negative.
          ||((accumulator == 0) && (cond == 1))    // Skip if accumulator zero.
          ||((accumulator > 0) && (cond == 2))) {  // Skip if accumulator positive.
       regPC.setValue(regPC.getValue()+1);
       if (fatalError)
         return; 
     }
   } // skipCond()


  void jump() { 
/******************************************************************************************
*   Move the value in the instruction's lower 12 bits to the PC (which always             *
*   contains the memory address of the next instruction to execute).                      *
******************************************************************************************/
     int addr = regIR.getValue();
     addr = addr & 0x0FFF;        // Strip the opcode from the instruction,
     regPC.setValue(addr);        // leaving the address.
     if (fatalError)
       return; 
   } // jump()


  void clear() { 
/******************************************************************************************
*   Clears the accumulator.                                                               *
******************************************************************************************/
     regAC.setValue(0);
   } // clear()


  void addI() { 
/******************************************************************************************
*   addI adds to the accumulator the value that is found in memory at the location        *
*   pointed to by the memory address in the MBR. So to get the augend, we need to         *
*   get the address of the augend and put it in the MAR, and then pull the                *
*   augend into the MBR so it can be added using the add() instruction.                   *
******************************************************************************************/
     regMAR.setValue(regMBR.getValue());
     if (fatalError) {
       return;
     }
     int addr = regMAR.getValue();
     int memoryRow = addr / 16;
     int memoryCol = addr % 16 + 1;
     try {
           regMBR.setValue(" "+memoryArray[memoryRow][memoryCol]); 
           add();
     }
     catch (ArrayIndexOutOfBoundsException e) {
             errorCode = 3;
             fatalError = true;
             return;
     }
   } // addI()


  void jumpI() { 
/******************************************************************************************
*   Similar to ADDI, the address of the address to jump to can be found at the            *
*   address to which the MBR is pointing.  After the fetch cycle, the MBR                 *
*   contains the address to jump to.  Notice that unlike the JUMP instruction,            *
*   this instruction takes a memory operand.                                              *
******************************************************************************************/
     regPC.setValue(regMBR.getValue());
     if (fatalError)
       return; 
   } // jumpI()


  void loadI() { 
/******************************************************************************************
*   loadI loads into the accumulator the value that is found in memory at the location    *
*   pointed to by the memory address in the MBR. We thus get the address of the value     *
*   to be loaded and put it in the MAR. This address is then used to retrieve the         *
*   actual value to be loaded, which happens using a call to the laod() method.           *
******************************************************************************************/
     int memoryRow, memoryCol;
     
     regMAR.setValue(regMBR.getValue());
     if (fatalError) {
       return;
     }
     int addr = regMAR.getValue();
     memoryRow = addr / 16;
     memoryCol = addr % 16 + 1;
     try {
           regMBR.setValue(" "+memoryArray[memoryRow][memoryCol]); 
           load();
     }
     catch (ArrayIndexOutOfBoundsException e) {
             errorCode = 3;
             fatalError = true;
             return;
     }
   } // loadI()

  void storeI() { 
/******************************************************************************************
*   storeI stores the value in the accumulator to the memory address located at the       *
*   address pointed to by the operand of the instruction. This msans that we have to      *
*   first retreive the value stored at the location pointed to by the operand and then    *
*   use that address to store the value that's in the accumulator.                        *
******************************************************************************************/
     int memoryRow, memoryCol;
     
     regMAR.setValue(regMBR.getValue());   // MBR contains the operand.
     if (fatalError) {
       return;
     }
     int addr = regMAR.getValue();        // The operand is the address of the 
     memoryRow = addr / 16;               // value that is the address of where
     memoryCol = addr % 16 + 1;           // we will store the contents AC. 
     try {
           regMBR.setValue(" "+memoryArray[memoryRow][memoryCol]); 
           store();                       // So store the value in the AC.
         }  
     catch (ArrayIndexOutOfBoundsException e) {
             errorCode = 3;
             fatalError = true;
     }
   
   } // storeI()

/* --                                                                                 -- */
/* --  Marie execution control methods.                                               -- */
/* --                                                                                 -- */
  void runToBreakpoint() {
/******************************************************************************************
*   If we have a runnable program loaded, we will run instructions until we encounter a   *
*   breakpoint or the program terminates.  The tricky part is to capture the condition    *
*   where we have just resumed from a previous breakpoint condition.  This method sets    *
*   a boolean variable, "resumed," to toggle past the first instruction executed after    *
*   a previous breakpoint pause.                                                          *
******************************************************************************************/
     Runnable runIt = new Runnable() {         // Create a thread in which to run.
       int lastStatementRun;                   // Hold the value of the PC for the
       Boolean isBreakpoint;                   // instruction we will run.
       String aString;
       public void run() {
         machineState = MARIE_RUNNING;
         while ((machineState == MARIE_RUNNING) && (!fatalError)) {
           aString = regPC.toString().trim();           // Move the cursor.
           if (codeReference.containsKey(aString)) {
             lastStatementRun =((Integer) codeReference.get(aString)).intValue();
           }
           fetchNext();
           try {                              // Give the user a chance to abort and also
             Thread.sleep(delay);             // a chance to see what's happening.
           }
           catch (InterruptedException e) {
           }
           if (!fatalError) {
             execute();
           }
           isBreakpoint = (Boolean) programArray[lastStatementRun][0];
           if ((machineState == MARIE_RUNNING) 
               && (isBreakpoint.booleanValue()))  {    // Check for a breakpoint.
             machineState = MARIE_PAUSED;              // If we find one, pause.
             setStatusMessage(" Stopped for breakpoint."); 
           }
         } // while
       } // run()
     }; // runIt
   if ((machineState == MARIE_UNINITIALIZED) ||
        (machineState == MARIE_NO_PROGRAM_LOADED))
     return;
   if ((machineState == MARIE_HALTED_NORMAL) ||
        (machineState == MARIE_HALTED_ABNORMAL))
     restart();
   fatalError = false;
   breakpointOn = true;
   Thread runThread = new Thread(runIt);         // Run this in a thread.
   runThread.start();                            // Fire it off.
   if (fatalError)                               // Stop on errors.
     halt();
  } // runToBreakpoint()


  void clearBreakPoints() {
/******************************************************************************************
*   Unconditionally removes all breakpoints from the programArray.                        *
******************************************************************************************/
    for (int i = 0; i < codeLineCount; i++)
      programArray[i][0] = new Boolean(false);
    breakpointOn = false;
} // clearBreakPoints()


  void runProgram() {
/******************************************************************************************
*   This method repeatedly invokes the fetch-execute cycle of the simulator until a the   *
*   program stops or a fatal error is encountered.                                        *
******************************************************************************************/
   breakpointOn = false;
   while ((machineState == MARIE_RUNNING) && (!fatalError)) {
     fetchNext();
     if (!fatalError) {
       execute();
     }
    } // while
    if (fatalError) {
      halt();
    }
  } // runProgram()


  public static void runInterpreter(String aFileName) {
/******************************************************************************************
*  This method is the mainline for the MARIE interpreter.  It expects to be passed the    *
*  name of a MARIE executable code file, <filename>, that will be opened as <filename>.MEX*
******************************************************************************************/
    MarieSim marieSim = new MarieSim();
  
    marieSim.getProgram(aFileName);
    marieSim.machineState = MARIE_RUNNING;
    marieSim.runProgram();
  } //runInterpreter

public static void main(String args[]) {
/******************************************************************************************
*  This main method runs the MARIE interpreter in standalone console mode by providing a  *
*  hook to the mainline processing method runInterpreter().  We do this so that the       *
*  interpreter can be used easily as a class method from another program.                 *
******************************************************************************************/
    runInterpreter(args[0]);
  } // main() 
} // MarieSim
