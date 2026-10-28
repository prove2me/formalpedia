-- Prove2me | solution 1 for H65K.Edge.piece23
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T08:16:07.97864+00:00
-- url     : https://prove2.me/submissions/59fa2bba-2446-46a7-8d57-76ff32a24356

import Definitions.Def_ArdaRH65K_Edge65000Data
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Arb4 Arb4.Q H65K.Edge

theorem solution :
    H11K.pieceJ E 23 = true := by
  decide +kernel
