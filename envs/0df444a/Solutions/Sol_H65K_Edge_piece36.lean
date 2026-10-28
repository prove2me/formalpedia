-- Prove2me | solution 1 for H65K.Edge.piece36
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T08:28:21.053187+00:00
-- url     : https://prove2.me/submissions/6987d54d-4aef-46c7-9681-d9a9f79074c5

import Definitions.Def_ArdaRH65K_Edge65000Data
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Arb4 Arb4.Q H65K.Edge

theorem solution :
    H11K.pieceJ E 36 = true := by
  decide +kernel
