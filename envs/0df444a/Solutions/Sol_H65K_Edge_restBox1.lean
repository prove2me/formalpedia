-- Prove2me | solution 1 for H65K.Edge.restBox1
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T08:33:32.412001+00:00
-- url     : https://prove2.me/submissions/e999ee62-1cb7-4512-9579-cb1cb22d1e60

import Definitions.Def_ArdaRH65K_Edge65000Data
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Arb4 Arb4.Q H65K.Edge

theorem solution :
    boxOK E.tn E.tq E.N (E.pc (E.m - 1)) E.D1 E.reLo1 E.reHi1 E.imLo1 E.imHi1 E.Qp1 E.Rn1 E.Rd1 E.qlo1 E.qhi1 = true := by
  decide +kernel
