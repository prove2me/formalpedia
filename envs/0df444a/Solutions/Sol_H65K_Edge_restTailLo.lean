-- Prove2me | solution 1 for H65K.Edge.restTailLo
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T08:36:24.342965+00:00
-- url     : https://prove2.me/submissions/f3a10c40-8a6f-4138-a200-373fea42b437

import Definitions.Def_ArdaRH65K_Edge65000Data
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Arb4 Arb4.Q H65K.Edge

theorem solution :
    finalLoOK ((E.pc (E.m - 1)).kk - (E.pc 0).kk) E.qhi0 E.qlo1 E.Lo = true := by
  decide +kernel
