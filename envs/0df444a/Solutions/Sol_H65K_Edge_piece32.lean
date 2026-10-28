-- Prove2me | solution 1 for H65K.Edge.piece32
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T08:24:28.121837+00:00
-- url     : https://prove2.me/submissions/1449e059-cd69-4674-b967-e3ad7bac659f

import Definitions.Def_ArdaRH65K_Edge65000Data
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Arb4 Arb4.Q H65K.Edge

theorem solution :
    H11K.pieceJ E 32 = true := by
  decide +kernel
