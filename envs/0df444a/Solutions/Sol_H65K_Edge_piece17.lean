-- Prove2me | solution 1 for H65K.Edge.piece17
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:53:00.706221+00:00
-- url     : https://prove2.me/submissions/1963333d-bea1-4438-afff-0671b0001fc0

import Definitions.Def_ArdaRH65K_Edge65000Data
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Arb4 Arb4.Q H65K.Edge

theorem solution :
    H11K.pieceJ E 17 = true := by
  decide +kernel
