-- Prove2me | solution 1 for H65K.Edge.piece05
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:24:16.869413+00:00
-- url     : https://prove2.me/submissions/667c611a-e9e4-413d-b612-03b1eae037f0

import Definitions.Def_ArdaRH65K_Edge65000Data
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Arb4 Arb4.Q H65K.Edge

theorem solution :
    H11K.pieceJ E 5 = true := by
  decide +kernel
