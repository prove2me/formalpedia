-- Prove2me | solution 1 for H65K.Edge.piece35
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T08:26:59.986972+00:00
-- url     : https://prove2.me/submissions/f9d3924d-69ce-4bcc-b93d-811f9084985e

import Definitions.Def_ArdaRH65K_Edge65000Data
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Arb4 Arb4.Q H65K.Edge

theorem solution :
    H11K.pieceJ E 35 = true := by
  decide +kernel
