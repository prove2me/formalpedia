-- Prove2me | solution 1 for H65K.Edge.piece21
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:57:36.017756+00:00
-- url     : https://prove2.me/submissions/a8f40fa9-5cdc-4181-be8e-6729657af2a6

import Definitions.Def_ArdaRH65K_Edge65000Data
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Arb4 Arb4.Q H65K.Edge

theorem solution :
    H11K.pieceJ E 21 = true := by
  decide +kernel
