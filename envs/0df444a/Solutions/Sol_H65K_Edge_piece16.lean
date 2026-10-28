-- Prove2me | solution 1 for H65K.Edge.piece16
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T08:02:45.927805+00:00
-- url     : https://prove2.me/submissions/d4980cab-2bd7-4f98-a70a-3f59a489762b

import Definitions.Def_ArdaRH65K_Edge65000Data
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Arb4 Arb4.Q H65K.Edge

theorem solution :
    H11K.pieceJ E 16 = true := by
  decide +kernel
