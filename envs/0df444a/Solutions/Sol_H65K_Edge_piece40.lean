-- Prove2me | solution 1 for H65K.Edge.piece40
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T08:32:26.474854+00:00
-- url     : https://prove2.me/submissions/5b5f0cf5-8faf-4946-b205-0869d8ccb748

import Definitions.Def_ArdaRH65K_Edge65000Data
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Arb4 Arb4.Q H65K.Edge

theorem solution :
    H11K.pieceJ E 40 = true := by
  decide +kernel
