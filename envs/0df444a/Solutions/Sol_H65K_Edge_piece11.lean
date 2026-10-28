-- Prove2me | solution 1 for H65K.Edge.piece11
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:28:02.683995+00:00
-- url     : https://prove2.me/submissions/cb9855ba-cb89-49e4-9ac5-359a8192f65f

import Definitions.Def_ArdaRH65K_Edge65000Data
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Arb4 Arb4.Q H65K.Edge

theorem solution :
    H11K.pieceJ E 11 = true := by
  decide +kernel
