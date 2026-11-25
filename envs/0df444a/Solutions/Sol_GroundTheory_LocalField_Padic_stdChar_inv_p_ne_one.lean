-- Prove2me | solution 1 for GroundTheory.LocalField.Padic.stdChar_inv_p_ne_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:06:59.178461+00:00
-- url     : https://prove2.me/submissions/f5677c40-6eeb-4723-884f-da9dffeb5477

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalFourierTrace
import Definitions.Def_GroundTheory_LocalFields_LocalFourierPadic
import Theorems.Thm_GroundTheory_LocalField_Padic_stdChar_intCast_div_pow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open ValuativeRel MeasureTheory
open scoped NNReal ENNReal
open GroundTheory.LocalField.Padic
variable (p : ℕ) [hp : Fact p.Prime]
namespace GroundTheory.LocalField.Padic
theorem _root_.solution : stdChar p (p : ℚ_[p])⁻¹ ≠ 1 := by
  have h := stdChar_intCast_div_pow p 1 1
  rw [Int.cast_one, pow_one, one_div] at h
  rw [h, Real.fourierChar_apply', Ne, Circle.exp_eq_one]
  rintro ⟨n, hn⟩
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have h1 : (1 : ℝ) = n * p := by
    push_cast at hn
    field_simp at hn
    nlinarith [Real.pi_pos]
  have h2 : (n : ℤ) * p = 1 := by exact_mod_cast h1.symm
  have h3 : (p : ℤ) = 1 := Int.eq_one_of_dvd_one (by positivity) ⟨n, by rw [← h2]; ring⟩
  have : p = 1 := by exact_mod_cast h3
  exact hp.out.one_lt.ne' this
end GroundTheory.LocalField.Padic
