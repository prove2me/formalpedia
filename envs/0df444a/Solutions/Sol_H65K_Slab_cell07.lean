-- Prove2me | solution 1 for H65K.Slab.cell07
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T08:42:15.100625+00:00
-- url     : https://prove2.me/submissions/9094a73c-364b-4d6b-aacd-2ce223a3bb33

import Definitions.Def_ArdaRH65K_Slab65000Data
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Arb4 Arb4.Q H65K.Slab

theorem solution :
    Arb4.cellOK S 7 = true := by
  decide +kernel
