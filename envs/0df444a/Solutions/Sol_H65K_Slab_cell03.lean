-- Prove2me | solution 1 for H65K.Slab.cell03
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T08:38:26.869393+00:00
-- url     : https://prove2.me/submissions/7d1cb98b-6290-4480-95b4-53f006ff8c73

import Definitions.Def_ArdaRH65K_Slab65000Data
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Arb4 Arb4.Q H65K.Slab

theorem solution :
    Arb4.cellOK S 3 = true := by
  decide +kernel
