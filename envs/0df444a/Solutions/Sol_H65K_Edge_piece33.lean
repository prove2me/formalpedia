-- Prove2me | solution 1 for H65K.Edge.piece33
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T08:25:06.290485+00:00
-- url     : https://prove2.me/submissions/e1d5f11a-38d5-4b93-82ef-93f2e19d1bae

import Definitions.Def_ArdaRH65K_Edge65000Data
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Arb4 Arb4.Q H65K.Edge

theorem solution :
    H11K.pieceJ E 33 = true := by
  decide +kernel
