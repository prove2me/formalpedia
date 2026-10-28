-- Prove2me | solution 1 for H65K.Slab.cell02
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T08:37:39.801874+00:00
-- url     : https://prove2.me/submissions/658b663c-0a1c-460b-9002-aa42c628b366

import Definitions.Def_ArdaRH65K_Slab65000Data
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Arb4 Arb4.Q H65K.Slab

theorem solution :
    Arb4.cellOK S 2 = true := by
  decide +kernel
