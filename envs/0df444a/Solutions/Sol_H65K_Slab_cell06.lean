-- Prove2me | solution 1 for H65K.Slab.cell06
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T08:41:32.593929+00:00
-- url     : https://prove2.me/submissions/90294e07-a352-41d9-84fe-80101e8b44dd

import Definitions.Def_ArdaRH65K_Slab65000Data
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Arb4 Arb4.Q H65K.Slab

theorem solution :
    Arb4.cellOK S 6 = true := by
  decide +kernel
