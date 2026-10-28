-- Prove2me | solution 1 for H65K.Edge.piece37
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T08:29:52.582048+00:00
-- url     : https://prove2.me/submissions/64750370-dfd3-451d-b842-7de63687303f

import Definitions.Def_ArdaRH65K_Edge65000Data
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Arb4 Arb4.Q H65K.Edge

theorem solution :
    H11K.pieceJ E 37 = true := by
  decide +kernel
