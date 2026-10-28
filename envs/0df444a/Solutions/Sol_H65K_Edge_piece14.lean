-- Prove2me | solution 1 for H65K.Edge.piece14
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:49:56.443525+00:00
-- url     : https://prove2.me/submissions/1e837598-1ea9-4798-baf3-b1b62e0da0a9

import Definitions.Def_ArdaRH65K_Edge65000Data
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Arb4 Arb4.Q H65K.Edge

theorem solution :
    H11K.pieceJ E 14 = true := by
  decide +kernel
