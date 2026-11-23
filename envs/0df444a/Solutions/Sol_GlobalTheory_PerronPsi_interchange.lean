-- Prove2me | solution 1 for GlobalTheory.PerronPsi.interchange
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:49:48.752535+00:00
-- url     : https://prove2.me/submissions/2ff58aae-4f4a-470f-abfa-a29f68d0e062

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_TruncatedPerronKernel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_TruncatedPerronPsi
import Theorems.Thm_GlobalTheory_PerronKernel_hbound
import Theorems.Thm_GlobalTheory_PerronKernel_ne_zero_of_re


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open GlobalTheory GlobalTheory.PerronPsi
namespace GlobalTheory.PerronPsi
theorem _root_.solution (a : ℕ → ℂ) (ha0 : a 0 = 0) {c u : ℝ} (T : ℝ) (hc : 0 < c) (hu : 0 < u)
    (hs : LSeriesSummable a c) :
    HasSum (fun n : ℕ => a n * ∫ t in (-T)..T,
        ((u / n : ℝ) : ℂ) ^ ((c : ℂ) + t * I) / ((c : ℂ) + t * I))
      (∫ t in (-T)..T, LSeries a ((c : ℂ) + t * I) * (u : ℂ) ^ ((c : ℂ) + t * I)
        / ((c : ℂ) + t * I)) := by
  have hsne : ∀ t : ℝ, (c : ℂ) + t * I ≠ 0 := fun t => GlobalTheory.PerronKernel.ne_zero_of_re hc.ne'
  have hsc : Continuous (fun t : ℝ => (c : ℂ) + t * I) := by fun_prop
  have hre : ∀ t : ℝ, ((c : ℂ) + t * I).re = c := fun t => by simp
  set F : ℕ → ℝ → ℂ := fun n t => LSeries.term a ((c : ℂ) + t * I) n
    * ((u : ℂ) ^ ((c : ℂ) + t * I) / ((c : ℂ) + t * I)) with hF
  have hsum_eq : ∀ n : ℕ, a n * ∫ t in (-T)..T,
      ((u / n : ℝ) : ℂ) ^ ((c : ℂ) + t * I) / ((c : ℂ) + t * I) = ∫ t in (-T)..T, F n t := by
    intro n
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t _
    simp only [hF]
    rcases eq_or_ne n 0 with rfl | hn
    · simp [ha0]
    · rw [LSeries.term_of_ne_zero hn]
      have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
      have harg : ((n : ℝ) : ℂ).arg ≠ Real.pi := by
        rw [Complex.arg_ofReal_of_nonneg hn0.le]
        exact Real.pi_ne_zero.symm
      have hdiv : (u / n : ℝ) = u * (n : ℝ)⁻¹ := div_eq_mul_inv _ _
      have hcp : ((u / n : ℝ) : ℂ) ^ ((c : ℂ) + t * I)
          = (u : ℂ) ^ ((c : ℂ) + t * I) / (n : ℂ) ^ ((c : ℂ) + t * I) := by
        rw [hdiv, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hu.le (inv_nonneg.2 hn0.le),
          Complex.ofReal_inv, Complex.inv_cpow _ _ harg, ← div_eq_mul_inv, Complex.ofReal_natCast]
      rw [hcp]
      ring
  have hS : ∀ t : ℝ, LSeriesSummable a ((c : ℂ) + t * I) :=
    fun t => hs.of_re_le_re (by simp)
  have hlim : ∀ t : ℝ, HasSum (fun n => F n t)
      (LSeries a ((c : ℂ) + t * I) * ((u : ℂ) ^ ((c : ℂ) + t * I) / ((c : ℂ) + t * I))) :=
    fun t => HasSum.mul_right _ (hS t).LSeriesHasSum
  have hbound : ∀ n t, ‖F n t‖ ≤ ‖LSeries.term a (c : ℂ) n‖ * (u ^ c / c) := by
    intro n t
    simp only [hF]
    rw [norm_mul, norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hu, hre t, LSeries.norm_term_eq,
      LSeries.norm_term_eq, hre t, Complex.ofReal_re]
    apply mul_le_mul_of_nonneg_left _ (by split_ifs <;> positivity)
    have h1 := Complex.re_le_norm ((c : ℂ) + t * I)
    rw [hre t] at h1
    exact div_le_div_of_nonneg_left (by positivity) hc h1
  have hcont : ∀ n, Continuous (F n) := by
    intro n
    simp only [hF]
    have h2 : Continuous fun t : ℝ => (u : ℂ) ^ ((c : ℂ) + t * I) / ((c : ℂ) + t * I) :=
      (hsc.const_cpow (Or.inl (by exact_mod_cast hu.ne'))).div hsc hsne
    refine Continuous.mul ?_ h2
    rcases eq_or_ne n 0 with rfl | hn
    · simp only [LSeries.term_zero]
      exact continuous_const
    · simp only [LSeries.term_of_ne_zero hn]
      exact continuous_const.div (hsc.const_cpow (Or.inl (by exact_mod_cast hn)))
        (fun t => by simp [hn])
  have key := intervalIntegral.hasSum_integral_of_dominated_convergence (μ := MeasureTheory.volume)
    (a := -T) (b := T) (F := F)
    (f := fun t => LSeries a ((c : ℂ) + t * I) * ((u : ℂ) ^ ((c : ℂ) + t * I) / ((c : ℂ) + t * I)))
    (fun n _ => ‖LSeries.term a (c : ℂ) n‖ * (u ^ c / c))
    (fun n => (hcont n).aestronglyMeasurable)
    (fun n => Filter.Eventually.of_forall (fun t _ => hbound n t))
    (Filter.Eventually.of_forall (fun _ _ => (summable_norm_iff.2 hs).mul_right _))
    intervalIntegrable_const
    (Filter.Eventually.of_forall (fun t _ => hlim t))
  have e1 : (fun n : ℕ => a n * ∫ t in (-T)..T,
      ((u / n : ℝ) : ℂ) ^ ((c : ℂ) + t * I) / ((c : ℂ) + t * I))
      = fun n => ∫ t in (-T)..T, F n t := funext hsum_eq
  have e2 : ∫ t in (-T)..T, LSeries a ((c : ℂ) + t * I) * (u : ℂ) ^ ((c : ℂ) + t * I) / ((c : ℂ) + t * I)
      = ∫ t in (-T)..T, LSeries a ((c : ℂ) + t * I) * ((u : ℂ) ^ ((c : ℂ) + t * I) / ((c : ℂ) + t * I)) := by
    apply intervalIntegral.integral_congr
    intro t _
    simp only
    rw [mul_div_assoc]
  rw [e1, e2]
  exact key
end GlobalTheory.PerronPsi
