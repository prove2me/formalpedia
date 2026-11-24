-- Prove2me | solution 1 for GlobalTheory.T.lt_one_of_power_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:18:24.579366+00:00
-- url     : https://prove2.me/submissions/f1670bc9-01a2-4db5-b81d-c3d8cd0724da

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LtOneOfPowerBound
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LtOneOfPowerBoundStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_Casselman_lt_one_of_inv_mul_sqrt_mul_rpow_two_lt_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (δ r : ℝ), 0 < δ → 0 ≤ r → δ⁻¹ * (Real.sqrt δ * r) ^ (2 : ℝ) < 1 → r < 1 := by
  first | exact @GlobalTheory.CompanionTheory.Casselman.lt_one_of_inv_mul_sqrt_mul_rpow_two_lt_one | exact GlobalTheory.CompanionTheory.Casselman.lt_one_of_inv_mul_sqrt_mul_rpow_two_lt_one | (intros; apply GlobalTheory.CompanionTheory.Casselman.lt_one_of_inv_mul_sqrt_mul_rpow_two_lt_one <;> assumption)
end _root_.GlobalTheory.T
