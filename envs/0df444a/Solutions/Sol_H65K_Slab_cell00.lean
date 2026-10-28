-- Prove2me | solution 1 for H65K.Slab.cell00
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T08:36:36.901224+00:00
-- url     : https://prove2.me/submissions/52eaa766-ca3c-4131-ba4e-fb2fbcd77bb3

import Definitions.Def_ArdaRH65K_Slab65000Data
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Arb4 Arb4.Q H65K.Slab

theorem solution :
    Arb4.cellOK S 0 = true := by
  decide +kernel
