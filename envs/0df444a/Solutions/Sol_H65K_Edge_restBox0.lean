-- Prove2me | solution 1 for H65K.Edge.restBox0
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T08:32:52.557714+00:00
-- url     : https://prove2.me/submissions/d02f967d-042f-44ba-84e4-23f8c562242d

import Definitions.Def_ArdaRH65K_Edge65000Data
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Arb4 Arb4.Q H65K.Edge

theorem solution :
    boxOK E.tn E.tq E.N (E.pc 0) E.D0 E.reLo0 E.reHi0 E.imLo0 E.imHi0 E.Qp0 E.Rn0 E.Rd0 E.qlo0 E.qhi0 = true := by
  decide +kernel
