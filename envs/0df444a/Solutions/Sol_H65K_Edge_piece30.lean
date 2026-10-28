-- Prove2me | solution 1 for H65K.Edge.piece30
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T08:22:59.510139+00:00
-- url     : https://prove2.me/submissions/3cb7d63f-f721-428c-a600-2212c218f59e

import Definitions.Def_ArdaRH65K_Edge65000Data
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Arb4 Arb4.Q H65K.Edge

theorem solution :
    H11K.pieceJ E 30 = true := by
  decide +kernel
