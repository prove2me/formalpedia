-- Prove2me | solution 1 for GlobalTheory.T.le_one_of_power_bounds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:17:03.699476+00:00
-- url     : https://prove2.me/submissions/4ce8552c-6110-45f1-bb25-abf718aee529

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LeOneOfPowerBounds
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LeOneOfPowerBoundsStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_Casselman_le_one_of_forall_sqrt_mul_rpow_lt


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
theorem _root_.solution : ∀ (δ r : ℝ), 0 < δ → δ < 1 → 0 ≤ r → (∀ ε : ℝ, 0 < ε → δ⁻¹ * (Real.sqrt δ * r) ^ (2 + ε) < 1) → r ≤ 1 := by
  first | exact @GlobalTheory.CompanionTheory.Casselman.le_one_of_forall_sqrt_mul_rpow_lt | exact GlobalTheory.CompanionTheory.Casselman.le_one_of_forall_sqrt_mul_rpow_lt | (intros; apply GlobalTheory.CompanionTheory.Casselman.le_one_of_forall_sqrt_mul_rpow_lt <;> assumption)
end _root_.GlobalTheory.T
