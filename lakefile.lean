import Lake
open Lake DSL

package LightData

lean_lib LightData

require YatimaStdLib from git
  "https://github.com/yatima-inc/YatimaStdLib.lean" @ "10f2b444390a41ede90ca5c038c6ff972014d433"

require LSpec from git
  "https://github.com/yatima-inc/lspec/" @ "88f7d23e56a061d32c7173cea5befa4b2c248b41"

lean_exe Tests.LightData
