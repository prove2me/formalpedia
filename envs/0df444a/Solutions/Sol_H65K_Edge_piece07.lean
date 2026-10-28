-- Prove2me | solution 1 for H65K.Edge.piece07
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:24:02.545843+00:00
-- url     : https://prove2.me/submissions/dcfa1ea1-65cc-4184-bdf3-37f26531608b

import Definitions.Def_ArdaRH65K_Edge65000Data
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Arb4 Arb4.Q H65K.Edge

theorem solution :
    H11K.pieceJ E 7 = true := by
  decide +kernel
