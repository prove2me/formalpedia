-- Prove2me | solution 1 for GlobalTheory.fourier_coeff_eq_zero_of_tsum_eq_zero_fin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:58:54.649218+00:00
-- url     : https://prove2.me/submissions/edd3ceab-9b13-41aa-b0bd-6e7db59325be

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_CoeffEqZeroOfHasSumMFourierOrthonormalImage
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_FourierCoeffEqZeroOfTsumEqZeroFin
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Complex Matrix
open scoped ContDiff BigOperators Real
namespace GlobalTheory
open Complex Matrix in
open scoped ContDiff BigOperators Real in
private lemma integral_Ioc_cexp_two_pi_I_int_mul (j : ℤ) :
    ∫ t, cexp (2 * π * I * (j : ℂ) * (t : ℂ)) ∂(MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) 1)) =
      if j = 0 then 1 else 0 := by
  rw [← intervalIntegral.integral_of_le zero_le_one]
  split_ifs with hj
  · subst hj; simp
  · have hc : (2 * π * I * (j : ℂ)) ≠ 0 := by
      have : (j : ℂ) ≠ 0 := by exact_mod_cast hj
      have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      simp [hπ, this, I_ne_zero]
    rw [integral_exp_mul_complex hc]
    have h1 : cexp (2 * π * I * (j : ℂ)) = 1 := by
      rw [show 2 * π * I * (j : ℂ) = j * (2 * π * I) by ring]
      exact exp_int_mul_two_pi_mul_I j
    simp [h1]
end GlobalTheory
end

set_option autoImplicit false
open Complex Matrix
open scoped ContDiff BigOperators Real
open GlobalTheory
open Complex Matrix
open scoped ContDiff BigOperators Real
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution :
    ∀ (n : ℕ) (c : (Fin n → ℤ) → ℂ), Summable (fun ν => ‖c ν‖) →
      (∀ x : Fin n → ℝ, ∑' ν, c ν * cexp (2 * π * I * ∑ k, (ν k : ℂ) * (x k : ℂ)) = 0) →
      ∀ ν, c ν = 0 := by
  intro n c hc h μ
  set m : MeasureTheory.Measure ℝ := MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) 1) with hm
  haveI : MeasureTheory.IsProbabilityMeasure m := ⟨by simp [m]⟩
  set P : MeasureTheory.Measure (Fin n → ℝ) := MeasureTheory.Measure.pi fun _ => m
  set G : (Fin n → ℤ) → (Fin n → ℝ) → ℂ := fun ν x =>
    c ν * ∏ k, cexp (2 * π * I * (((ν k - μ k : ℤ)) : ℂ) * (x k : ℂ)) with hG
  have hnorm : ∀ ν x, ‖G ν x‖ = ‖c ν‖ := by
    intro ν x
    simp only [G, norm_mul, norm_prod, Complex.norm_exp]
    simp [Complex.mul_re]
  have hint : ∀ ν, MeasureTheory.Integrable (G ν) P := by
    intro ν
    refine MeasureTheory.Integrable.of_bound (Continuous.aestronglyMeasurable (by fun_prop))
      ‖c ν‖ (MeasureTheory.ae_of_all _ fun x => (hnorm ν x).le)
  have hval : ∀ ν, ∫ x, G ν x ∂P = if ν = μ then c ν else 0 := by
    intro ν
    simp only [G]
    rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_fintype_prod_eq_prod (E := fun _ => ℝ)
      (μ := fun _ => m) (fun k (t : ℝ) => cexp (2 * π * I * (((ν k - μ k : ℤ)) : ℂ) * (t : ℂ)))]
    simp only [hm, integral_Ioc_cexp_two_pi_I_int_mul]
    by_cases hνμ : ν = μ
    · subst hνμ; simp
    · obtain ⟨k, hk⟩ := Function.ne_iff.mp hνμ
      rw [if_neg hνμ, Finset.prod_eq_zero (Finset.mem_univ k) (by simp [sub_eq_zero, hk]), mul_zero]
  have hsum : ∀ x, ∑' ν, G ν x = 0 := by
    intro x
    have hx := h x
    have : ∀ ν, G ν x = c ν * cexp (2 * π * I * ∑ k, (ν k : ℂ) * (x k : ℂ)) *
        cexp (-(2 * π * I * ∑ k, (μ k : ℂ) * (x k : ℂ))) := by
      intro ν
      simp only [G, mul_assoc]
      congr 1
      rw [← Complex.exp_add, ← Complex.exp_sum]
      congr 1
      push_cast
      simp only [Finset.mul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun k _ => by ring
    simp only [this]
    rw [tsum_mul_right, hx, zero_mul]
  have key := MeasureTheory.integral_tsum_of_summable_integral_norm hint
    (by simpa [hnorm] using hc)
  simp only [hval, hsum, MeasureTheory.integral_zero] at key
  rwa [tsum_ite_eq] at key
end _root_.GlobalTheory
end GlobalTheory
