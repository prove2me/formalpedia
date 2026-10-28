-- Prove2me | solution 1 for H65K.Edge.piece25
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T08:17:27.834983+00:00
-- url     : https://prove2.me/submissions/3e7255a3-2580-42ef-881b-25aa91cc35cc

import Definitions.Def_ArdaRH65K_Edge65000Data
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Arb4 Arb4.Q H65K.Edge

theorem solution :
    H11K.pieceJ E 25 = true := by
  decide +kernel
