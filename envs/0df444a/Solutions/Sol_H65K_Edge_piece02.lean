-- Prove2me | solution 1 for H65K.Edge.piece02
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:19:41.102966+00:00
-- url     : https://prove2.me/submissions/5d97b869-a0fe-4cfa-a2cc-83fa431bdf78

import Definitions.Def_ArdaRH65K_Edge65000Data
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Arb4 Arb4.Q H65K.Edge

theorem solution :
    H11K.pieceJ E 2 = true := by
  decide +kernel
