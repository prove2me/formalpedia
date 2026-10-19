-- Prove2me | solution 1 for OAI.GaussianPropeller.Reduction.recentered_norm_sq
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T06:10:17.926087+00:00
-- url     : https://prove2.me/submissions/0d9b0429-7e4a-4b99-82d3-788c7bc70d66

import Mathlib
import Definitions.Def_GaussianPropeller
import Definitions.Def_OAI_Probability_GaussianPropeller_Moments
import Definitions.Def_OAI_Probability_GaussianPropeller_Dual
import Definitions.Def_OAI_Probability_GaussianPropeller_Deletion

open OAI OAI.GaussianPropeller OAI.GaussianPropeller.Reduction
open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
variable {d k : ℕ} [NeZero k]


omit [NeZero k] in
theorem solution (hk : 2 ≤ k) (z : Fin k → Space d)
    (hz : ∑ j, z j = 0) (i : Fin k) :
    ‖recentered z i‖^2 = (∑ j, ‖z j‖^2) -
      ((k:ℝ)/((k:ℝ)-1)) * ‖z i‖^2 := by
  classical
  set c : ℝ := ((k:ℝ)-1)⁻¹ with hc
  have hk1 : (1:ℝ) < k := by exact_mod_cast hk
  have hk0 : (k:ℝ) - 1 ≠ 0 := by linarith
  rw [PiLp.norm_sq_eq_of_L2]
  simp only [recentered, PiLp.toLp_apply]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), ← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  simp only [if_true, norm_zero]
  rw [show (0:ℝ)^2 = 0 by norm_num, zero_add]
  have hrest : ∀ j ∈ Finset.univ.erase i, ‖(if j = i then (0 : Space d) else z j + c • z i)‖ ^ 2
      = ‖z j‖^2 + 2 * (c * ⟪z j, z i⟫) + c^2 * ‖z i‖^2 := by
    intro j hj
    rw [if_neg (Finset.ne_of_mem_erase hj), norm_add_sq_real, inner_smul_right, norm_smul,
      mul_pow, Real.norm_eq_abs, sq_abs]
  rw [Finset.sum_congr rfl hrest, Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, ← sum_inner, Finset.sum_const]
  have hs : ∑ j ∈ Finset.univ.erase i, z j = - z i := by
    rw [eq_neg_iff_add_eq_zero, add_comm, Finset.add_sum_erase _ _ (Finset.mem_univ i), hz]
  rw [hs, inner_neg_left, real_inner_self_eq_norm_sq, Finset.card_erase_of_mem (Finset.mem_univ _),
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hcast : ((k - 1 : ℕ) : ℝ) = (k:ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; simp
  rw [hcast]
  have : (k:ℝ)/((k:ℝ)-1) = 1 + c := by rw [hc]; field_simp; ring
  rw [this]
  have : ((k:ℝ) - 1) * (c^2 * ‖z i‖^2) = c * ‖z i‖^2 := by rw [hc]; field_simp
  rw [this]
  ring

