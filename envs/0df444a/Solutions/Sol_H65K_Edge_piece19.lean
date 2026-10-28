-- Prove2me | solution 1 for H65K.Edge.piece19
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:55:06.981527+00:00
-- url     : https://prove2.me/submissions/c6617c7c-5366-46a1-88f6-ffed16590d4f

import Definitions.Def_ArdaRH65K_Edge65000Data
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Arb4 Arb4.Q H65K.Edge

theorem solution :
    H11K.pieceJ E 19 = true := by
  decide +kernel
