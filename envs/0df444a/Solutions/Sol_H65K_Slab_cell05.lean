-- Prove2me | solution 1 for H65K.Slab.cell05
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T08:40:56.893025+00:00
-- url     : https://prove2.me/submissions/2f274879-b073-4958-9e27-abd74c248da0

import Definitions.Def_ArdaRH65K_Slab65000Data
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Arb4 Arb4.Q H65K.Slab

theorem solution :
    Arb4.cellOK S 5 = true := by
  decide +kernel
