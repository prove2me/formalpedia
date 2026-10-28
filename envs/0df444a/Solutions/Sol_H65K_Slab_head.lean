-- Prove2me | solution 1 for H65K.Slab.head
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T08:44:23.074571+00:00
-- url     : https://prove2.me/submissions/2c9587ac-a87d-406f-8e67-a66bee8a9ea0

import Definitions.Def_ArdaRH65K_Slab65000Data
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Arb4 Arb4.Q H65K.Slab

theorem solution :
    Arb4.slabHeadOK S = true := by
  decide +kernel
