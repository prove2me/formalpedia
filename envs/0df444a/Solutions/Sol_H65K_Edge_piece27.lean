-- Prove2me | solution 1 for H65K.Edge.piece27
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T08:20:21.136094+00:00
-- url     : https://prove2.me/submissions/aa77afb3-6609-4a6b-866f-0375f8c5f4c4

import Definitions.Def_ArdaRH65K_Edge65000Data
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Arb4 Arb4.Q H65K.Edge

theorem solution :
    H11K.pieceJ E 27 = true := by
  decide +kernel
