-- Prove2me | solution 1 for GlobalTheory.cumulant_lower_bound_of_bounded_centred
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:43:35.241626+00:00
-- url     : https://prove2.me/submissions/1b58f72e-1092-40a0-8e77-80e6621caab3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExpQuadraticLowerAndLogLinearLowerStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CumulantLowerBoundOfBoundedCentred
import Theorems.Thm_P2M_GlobalTheory_T_exp_quadratic_lower_and_log_linear_lower__a63618dbfd89


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Real
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (ι : Type) [Fintype ι] (w y : ι → ℝ) (R : ℝ), 0 < R → (∀ J, 0 ≤ w J) → ∑ J, w J = 1 →
      ∑ J, w J * y J = 0 → (∀ J, w J ≠ 0 → |y J| ≤ R) →
      min 1 (1 / R) * (∑ J, w J * y J ^ 2) / 4 ≤ Real.log (∑ J, w J * Real.exp (y J)) := by
  intro ι _ w y R hR hw hs hm hb
  obtain ⟨hexp, hlog⟩ := GlobalTheory.T.exp_quadratic_lower_and_log_linear_lower'
  set t : ℝ := min 1 (1 / R) with ht
  set V : ℝ := ∑ J, w J * y J ^ 2 with hV
  set S : ℝ := ∑ J, w J * Real.exp (y J) with hS
  have ht0 : 0 < t := lt_min one_pos (by positivity)
  have ht1 : t ≤ 1 := min_le_left _ _
  have htR : t * R ≤ 1 := by
    have : t ≤ 1 / R := min_le_right _ _
    rwa [le_div_iff₀ hR] at this
  have hty : ∀ J, w J ≠ 0 → |t * y J| ≤ 1 := by
    intro J hJ
    rw [abs_mul, abs_of_pos ht0]
    exact (mul_le_mul_of_nonneg_left (hb J hJ) ht0.le).trans htR
  have hV0 : 0 ≤ V := Finset.sum_nonneg fun J _ => mul_nonneg (hw J) (sq_nonneg _)
  have htV : t ^ 2 * V ≤ 1 := by
    rw [hV, Finset.mul_sum, ← hs]
    refine Finset.sum_le_sum fun J _ => ?_
    by_cases hJ : w J = 0
    · simp [hJ]
    · have h1 : (t * y J) ^ 2 ≤ 1 := (sq_le_one_iff_abs_le_one _).2 (hty J hJ)
      have := mul_le_mul_of_nonneg_left h1 (hw J)
      nlinarith
  have hlow : 1 + t ^ 2 * V / 3 ≤ ∑ J, w J * Real.exp (t * y J) := by
    have e : 1 + t ^ 2 * V / 3 = ∑ J, w J * (1 + t * y J + (t * y J) ^ 2 / 3) := by
      have e2 : ∀ J, w J * (1 + t * y J + (t * y J) ^ 2 / 3)
          = w J + t * (w J * y J) + t ^ 2 / 3 * (w J * y J ^ 2) := fun J => by ring
      simp only [e2, Finset.sum_add_distrib, ← Finset.mul_sum, hs, hm]
      rw [← hV]; ring
    rw [e]
    refine Finset.sum_le_sum fun J _ => ?_
    by_cases hJ : w J = 0
    · simp [hJ]
    · exact mul_le_mul_of_nonneg_left (hexp _ (hty J hJ)) (hw J)
  have hS1 : 1 ≤ S := by
    have : ∑ J, w J * (y J + 1) = 1 := by
      simp only [mul_add, mul_one, Finset.sum_add_distrib, hs, hm, zero_add]
    rw [← this]
    exact Finset.sum_le_sum fun J _ =>
      mul_le_mul_of_nonneg_left (Real.add_one_le_exp _) (hw J)
  have hS0 : 0 < S := by linarith
  set F : ℝ := Real.log S with hF
  have hEF : Real.exp F = S := Real.exp_log hS0
  have hpt : ∀ J, Real.exp (t * y J)
      ≤ Real.exp (t * F) * (t * (Real.exp (y J) / S) + (1 - t)) := by
    intro J
    have h := convexOn_exp.2 (Set.mem_univ (y J - F)) (Set.mem_univ 0) ht0.le
      (sub_nonneg.2 ht1) (by ring)
    simp only [smul_eq_mul, mul_zero, add_zero, Real.exp_zero, mul_one] at h
    rw [Real.exp_sub, hEF] at h
    have e : t * y J = t * F + t * (y J - F) := by ring
    rw [e, Real.exp_add]
    exact mul_le_mul_of_nonneg_left h (Real.exp_pos _).le
  have hup : ∑ J, w J * Real.exp (t * y J) ≤ Real.exp (t * F) := by
    calc ∑ J, w J * Real.exp (t * y J)
        ≤ ∑ J, w J * (Real.exp (t * F) * (t * (Real.exp (y J) / S) + (1 - t))) :=
          Finset.sum_le_sum fun J _ => mul_le_mul_of_nonneg_left (hpt J) (hw J)
      _ = ∑ J, (Real.exp (t * F) * t / S * (w J * Real.exp (y J))
            + Real.exp (t * F) * (1 - t) * w J) :=
          Finset.sum_congr rfl fun J _ => by ring
      _ = Real.exp (t * F) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hs, ← hS]
          field_simp
          ring
  have hu0 : 0 ≤ t ^ 2 * V / 3 := by positivity
  have h1 := hlog (t ^ 2 * V / 3) hu0 (by linarith)
  have h2 : Real.log (1 + t ^ 2 * V / 3) ≤ t * F := by
    rw [Real.log_le_iff_le_exp (by linarith)]
    exact hlow.trans hup
  have h3 : t * (t * V / 4) ≤ t * F := by nlinarith
  exact le_of_mul_le_mul_left h3 ht0
end GlobalTheory
