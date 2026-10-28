-- Prove2me | solution 1 for H65K.Edge.restTailHi
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T08:35:42.394987+00:00
-- url     : https://prove2.me/submissions/62cc5e62-49f1-45b3-8b2f-63cb3a76effb

import Definitions.Def_ArdaRH65K_Edge65000Data
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Arb4 Arb4.Q H65K.Edge

theorem solution :
    finalHiOK ((E.pc (E.m - 1)).kk - (E.pc 0).kk) E.qlo0 E.qhi1 E.Hi = true := by
  decide +kernel
