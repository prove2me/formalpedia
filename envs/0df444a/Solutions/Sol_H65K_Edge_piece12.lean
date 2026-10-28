-- Prove2me | solution 1 for H65K.Edge.piece12
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:31:13.628554+00:00
-- url     : https://prove2.me/submissions/05c0ca66-0035-4998-820c-ba5b34911f34

import Definitions.Def_ArdaRH65K_Edge65000Data
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Arb4 Arb4.Q H65K.Edge

theorem solution :
    H11K.pieceJ E 12 = true := by
  decide +kernel
