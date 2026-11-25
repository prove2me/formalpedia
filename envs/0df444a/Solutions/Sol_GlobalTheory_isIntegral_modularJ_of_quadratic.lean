-- Prove2me | solution 1 for GlobalTheory.isIntegral_modularJ_of_quadratic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T06:03:19.995117+00:00
-- url     : https://prove2.me/submissions/9d92a5a2-5c8c-4655-97b1-46ca84f4c0d2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsPolynomialModularJOfHasQExpansion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ModularJExpansionAndPolynomialAndIsIntegral
import Theorems.Thm_GlobalTheory_isIntegral_modularJ_of_fixed

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open UpperHalfPlane ModularForm Complex Function Filter PowerSeries
open scoped Topology MatrixGroups Manifold Real
noncomputable section
open GlobalTheory
local notation "𝕢" => Function.Periodic.qParam
namespace GlobalTheory
theorem _root_.solution {τ : ℍ} {a b c : ℤ} (ha : a ≠ 0)
    (h : a * (τ : ℂ) ^ 2 + b * τ + c = 0) : IsIntegral ℤ (modularJ τ) := by
  have hD : 0 < 4 * a * c - b ^ 2 := by
    have h1 := congrArg Complex.re h
    have h2 := congrArg Complex.im h
    simp [pow_two] at h1 h2
    have hy := τ.im_pos
    have h3 : (b : ℝ) = -2 * a * τ.re := by
      apply mul_right_cancel₀ hy.ne'
      linear_combination h2
    have h4 : (4 * a * c - b ^ 2 : ℝ) = (2 * a * τ.im) ^ 2 := by
      rw [h3] at h1 ⊢
      linear_combination 4 * a * h1
    have h5 : (a : ℝ) ≠ 0 := by exact_mod_cast ha
    have : (0 : ℝ) < 4 * a * c - b ^ 2 := by rw [h4]; positivity
    exact_mod_cast this
  set D := 4 * a * c - b ^ 2 with hD'
  set k := D + |b| with hk
  have hm : D ≤ 2 * k - b := by have := le_abs_self b; have := abs_nonneg b; omega
  have h4 : 4 * (k ^ 2 - b * k + a * c) = (2 * k - b) ^ 2 + D := by rw [hD']; ring
  obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ k ^ 2 - b * k + a * c by nlinarith)
  refine isIntegral_modularJ_of_fixed (n := n) ?_
    ⟨!![k - b, -c; a, k], by rw [← hn, Matrix.det_fin_two_of]; ring⟩ ?_
  · rintro ⟨r, hr⟩
    have h5 : (2 * r : ℤ) ^ 2 = (2 * k - b) ^ 2 + D := by
      rw [← h4, hn, hr]; push_cast; ring
    generalize 2 * k - b = m at *
    have h6 : m < 2 * r := by nlinarith
    nlinarith
  · simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one]
    push_cast
    linear_combination -h
end GlobalTheory
