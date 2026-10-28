-- Prove2me | solution 1 for H65K.Edge.piece03
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:18:43.483231+00:00
-- url     : https://prove2.me/submissions/bc43cc27-61dc-4194-8746-5a54d9578877

import Definitions.Def_ArdaRH65K_Edge65000Data
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Arb4 Arb4.Q H65K.Edge

theorem solution :
    H11K.pieceJ E 3 = true := by
  decide +kernel
