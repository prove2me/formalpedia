-- Prove2me | solution 1 for H65K.Edge.piece09
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:27:39.587272+00:00
-- url     : https://prove2.me/submissions/9ef15c1f-105d-4e0d-b8be-141e4b5c1802

import Definitions.Def_ArdaRH65K_Edge65000Data
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Arb4 Arb4.Q H65K.Edge

theorem solution :
    H11K.pieceJ E 9 = true := by
  decide +kernel
