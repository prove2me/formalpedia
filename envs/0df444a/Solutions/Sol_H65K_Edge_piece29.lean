-- Prove2me | solution 1 for H65K.Edge.piece29
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T08:21:29.195377+00:00
-- url     : https://prove2.me/submissions/fee530bf-fa0c-4998-b54c-b58f1d9db274

import Definitions.Def_ArdaRH65K_Edge65000Data
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Arb4 Arb4.Q H65K.Edge

theorem solution :
    H11K.pieceJ E 29 = true := by
  decide +kernel
