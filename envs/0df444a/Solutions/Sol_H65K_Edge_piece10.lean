-- Prove2me | solution 1 for H65K.Edge.piece10
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:27:50.902953+00:00
-- url     : https://prove2.me/submissions/84447082-da2c-44f0-8fa2-4aba92aaed03

import Definitions.Def_ArdaRH65K_Edge65000Data
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Arb4 Arb4.Q H65K.Edge

theorem solution :
    H11K.pieceJ E 10 = true := by
  decide +kernel
