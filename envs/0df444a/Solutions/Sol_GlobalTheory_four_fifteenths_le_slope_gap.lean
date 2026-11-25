-- Prove2me | solution 1 for GlobalTheory.four_fifteenths_le_slope_gap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:37:20.782651+00:00
-- url     : https://prove2.me/submissions/cce46f1b-b67e-41b7-b123-5eb0b2897678

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_DetPolyMulCayleyOmegaPow
import Definitions.Def_ReciprocityTheory_DualLattices_VEqZeroOfPowEqOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PeriodValuation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_FactorizationLeFourFifteenths

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.PGsh
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {x : ℝ} (hx : 5 ≤ x) {i : ℕ} (hi : 1 ≤ i) :
    4 / 15 ≤ (1 / (x ^ 2 - 1) + 1 / 2 - 1 / (8 * x ^ i)) - 1 / (x - 1) := by
  have h1 : x ≤ x ^ i := by
    simpa using pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ x) hi
  have h2 : 1 / (8 * x ^ i) ≤ 1 / 40 :=
    one_div_le_one_div_of_le (by norm_num) (by linarith)
  have hp : 0 < x ^ 2 - 1 := by nlinarith
  have hq : 0 < x - 1 := by linarith
  have h3 : 1 / (x - 1) - 1 / (x ^ 2 - 1) = x / (x ^ 2 - 1) := by
    have : x ^ 2 - 1 = (x - 1) * (x + 1) := by ring
    rw [this]
    have hr : 0 < x + 1 := by linarith
    field_simp
    ring
  have h4 : x / (x ^ 2 - 1) ≤ 5 / 24 := by
    rw [div_le_div_iff₀ hp (by norm_num)]
    nlinarith
  linarith
end GlobalTheory
