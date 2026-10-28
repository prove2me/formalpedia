-- Prove2me | solution 1 for H65K.Edge.piece31
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T08:23:53.030223+00:00
-- url     : https://prove2.me/submissions/27d66e69-90ed-44d3-8084-1a31eb14e49f

import Definitions.Def_ArdaRH65K_Edge65000Data
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Arb4 Arb4.Q H65K.Edge

theorem solution :
    H11K.pieceJ E 31 = true := by
  decide +kernel
