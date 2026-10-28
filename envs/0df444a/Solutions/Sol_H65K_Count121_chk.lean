-- Prove2me | solution 1 for H65K.Count121.chk
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:20:45.543836+00:00
-- url     : https://prove2.me/submissions/9d529b8f-56cd-45d1-b29d-34cfdc3b4b6b

import Definitions.Def_ArdaRH65K_Count121Data
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Arb4 Arb4.Q

theorem solution :
    (H11K.validBS (Q.ofNat 121) (Q.ofNat 65000) (Q.frac 65121 2)
      (Q.frac 4209284657 4) 85250 H65K.Count121.E &&
      k6sideB H65K.Count121.G0 H65K.Count121.G1 H65K.Count121.E) = true := by
  decide +kernel
