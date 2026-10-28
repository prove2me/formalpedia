-- Prove2me | solution 1 for H65K.Edge.piece24
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T08:17:08.786864+00:00
-- url     : https://prove2.me/submissions/13ed14a0-0511-4b0b-b89d-65a7e1c5a019

import Definitions.Def_ArdaRH65K_Edge65000Data
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Arb4 Arb4.Q H65K.Edge

theorem solution :
    H11K.pieceJ E 24 = true := by
  decide +kernel
