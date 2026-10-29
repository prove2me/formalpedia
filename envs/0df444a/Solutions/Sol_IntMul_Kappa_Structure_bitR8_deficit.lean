-- Prove2me | solution 1 for IntMul.Kappa.Structure.bitR8_deficit
-- status  : ACCEPTED   (prove)
-- author  : @darkhipo
-- created : 2026-10-28T20:37:11.818408+00:00
-- url     : https://prove2.me/submissions/9939474e-9fa1-425d-835a-b6bd47c109b0

import Definitions.Def_IntMul_KappaFramework
import Definitions.Def_IntMul_KappaJainData

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

open IntMul.Kappa

theorem solution :
    histRankSum Jain.bitR8 = 529 * 104719230 - 21 * (Nat.choose 23 2)^2 := by
  decide +kernel
