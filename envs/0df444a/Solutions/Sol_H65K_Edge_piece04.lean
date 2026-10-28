-- Prove2me | solution 1 for H65K.Edge.piece04
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:23:33.32059+00:00
-- url     : https://prove2.me/submissions/15be1028-a8a7-467d-9a04-3afecce65e95

import Definitions.Def_ArdaRH65K_Edge65000Data
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Arb4 Arb4.Q H65K.Edge

theorem solution :
    H11K.pieceJ E 4 = true := by
  decide +kernel
