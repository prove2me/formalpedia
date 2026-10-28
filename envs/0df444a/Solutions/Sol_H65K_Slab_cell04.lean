-- Prove2me | solution 1 for H65K.Slab.cell04
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T08:40:40.145119+00:00
-- url     : https://prove2.me/submissions/1e83dba8-c20e-46eb-ab71-7e9f61c593a0

import Definitions.Def_ArdaRH65K_Slab65000Data
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Arb4 Arb4.Q H65K.Slab

theorem solution :
    Arb4.cellOK S 4 = true := by
  decide +kernel
