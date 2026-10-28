-- Prove2me | solution 1 for H65K.Edge.piece28
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T08:20:45.840496+00:00
-- url     : https://prove2.me/submissions/27fd640b-ca92-4707-8383-09cf90258ab9

import Definitions.Def_ArdaRH65K_Edge65000Data
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Arb4 Arb4.Q H65K.Edge

theorem solution :
    H11K.pieceJ E 28 = true := by
  decide +kernel
