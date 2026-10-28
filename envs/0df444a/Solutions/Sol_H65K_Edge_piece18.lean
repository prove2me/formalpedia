-- Prove2me | solution 1 for H65K.Edge.piece18
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:53:36.76747+00:00
-- url     : https://prove2.me/submissions/b67ac6ff-d4d7-45c7-a8d6-f2abb67010fb

import Definitions.Def_ArdaRH65K_Edge65000Data
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Arb4 Arb4.Q H65K.Edge

theorem solution :
    H11K.pieceJ E 18 = true := by
  decide +kernel
