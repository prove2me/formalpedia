-- Prove2me | solution 1 for H65K.Edge.piece08
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:27:26.118974+00:00
-- url     : https://prove2.me/submissions/cdc290c4-9b65-4773-af56-e2ca17b07375

import Definitions.Def_ArdaRH65K_Edge65000Data
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Arb4 Arb4.Q H65K.Edge

theorem solution :
    H11K.pieceJ E 8 = true := by
  decide +kernel
