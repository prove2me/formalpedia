-- Prove2me | solution 1 for Helfgott.etaPlus_vonMangoldt_summable
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-04T22:33:10.987722+00:00
-- url     : https://prove2.me/submissions/058c3464-a216-4a96-857b-0829d114d00b

import Definitions.Def_Helfgott_Smoothings
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Tactic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Analysis.Complex.Basic

/-! Full actual etaPlus sum convergence proof, with Mellin inversion and Gaussian envelope. Written by Codex. -/

open MeasureTheory Set

namespace Helfgott

lemma mellin_inverse_weight (F : ℝ → ℝ) (w : ℝ) (hw : 0 < w) :
    w^(-2 : ℝ) * (F ((w^(-1 : ℝ))⁻¹)/(w^(-1 : ℝ))) = F w/w := by
  rw [Real.rpow_neg_one,inv_inv,Real.rpow_neg hw.le,Real.rpow_two]
  field_simp

theorem integral_mellin_inverse (F : ℝ → ℝ) :
    (∫ w in Ioi (0 : ℝ), F w/w) = ∫ w in Ioi (0 : ℝ), F w⁻¹/w := by
  have h := integral_comp_rpow_Ioi (fun w : ℝ => F w⁻¹/w) (p := (-1 : ℝ)) (by norm_num)
  norm_num only [abs_neg,abs_one,neg_sub,one_add_one_eq_two,smul_eq_mul,one_mul] at h
  rw [← h]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro w hw
  exact (mellin_inverse_weight F w hw).symm

theorem integrable_mellin_inverse (F : ℝ → ℝ) :
    IntegrableOn (fun w : ℝ => F w/w) (Ioi (0 : ℝ)) ↔
      IntegrableOn (fun w : ℝ => F w⁻¹/w) (Ioi (0 : ℝ)) := by
  have h := integrableOn_Ioi_comp_rpow_iff' (fun w : ℝ => F w⁻¹/w) (p := (-1 : ℝ)) (by norm_num)
  norm_num only [neg_sub,one_add_one_eq_two,smul_eq_mul] at h
  rw [← h]
  apply integrableOn_congr_fun _ measurableSet_Ioi
  intro w hw
  exact (mellin_inverse_weight F w hw).symm

end Helfgott

open MeasureTheory Set Filter

namespace Helfgott

private noncomputable def weightedMajorKernel (t : ℝ) : ℝ :=
  (Icc (0 : ℝ) 2).indicator (fun t => t*(2-t)^3*Real.exp (t-1/2)) t

private lemma weightedMajorKernel_nonneg (t : ℝ) : 0 ≤ weightedMajorKernel t := by
  by_cases ht : t ∈ Icc (0 : ℝ) 2
  · rw [weightedMajorKernel,indicator_of_mem ht]
    have h : 0 ≤ 2-t := by linarith [ht.2]
    have h0 : 0 ≤ t := ht.1
    positivity
  · simp [weightedMajorKernel,ht]

private lemma weightedMajorKernel_continuous : Continuous weightedMajorKernel := by
  unfold weightedMajorKernel
  apply continuous_indicator
  · intro t ht
    have hb := frontier_subset_closure ht
    rw [isClosed_Icc.closure_eq] at hb
    have hn : t ∉ interior (Icc (0 : ℝ) 2) := ht.2
    rw [interior_Icc] at hn
    have he : t=0 ∨ t=2 := by
      by_contra hh
      apply hn
      have h0 : t ≠ 0 := by tauto
      have h2 : t ≠ 2 := by tauto
      exact ⟨lt_of_le_of_ne hb.1 (Ne.symm h0),lt_of_le_of_ne hb.2 h2⟩
    rcases he with rfl | rfl <;> norm_num
  · exact (by fun_prop : Continuous (fun t : ℝ => t*(2-t)^3*Real.exp (t-1/2))).continuousOn

private lemma weightedMajorKernel_compact : HasCompactSupport weightedMajorKernel := by
  apply HasCompactSupport.intro (K := Icc (0 : ℝ) 2) isCompact_Icc
  intro t ht
  simp [weightedMajorKernel,ht]

private lemma weightedMajorKernel_integrable : Integrable weightedMajorKernel :=
  weightedMajorKernel_continuous.integrable_of_hasCompactSupport weightedMajorKernel_compact

private lemma majorKernel_eq_weighted (t : ℝ) : majorKernel t = t*weightedMajorKernel t := by
  by_cases ht : t ∈ Icc (0 : ℝ) 2
  · simp only [majorKernel,weightedMajorKernel,indicator_of_mem ht]
    ring
  · simp [majorKernel,weightedMajorKernel,ht]

lemma bandKernel_abs_le (H w : ℝ) : |bandKernel H w| ≤ |H|/Real.pi := by
  unfold bandKernel
  rw [abs_mul,abs_div,abs_of_pos Real.pi_pos]
  exact mul_le_of_le_one_right (by positivity) (Real.abs_sinc_le_one _)

private lemma inverse_major_integrand (H t v : ℝ) (hv : 0 < v) :
    majorKernel (t/v⁻¹)*bandKernel H v⁻¹/v =
      t*weightedMajorKernel (t*v)*bandKernel H v⁻¹ := by
  rw [div_inv_eq_mul,majorKernel_eq_weighted]
  field_simp

private lemma inverse_major_integrable (H t : ℝ) (ht : 0 < t) :
    IntegrableOn (fun v : ℝ => t*weightedMajorKernel (t*v)*bandKernel H v⁻¹) (Ioi (0 : ℝ)) := by
  have hk := weightedMajorKernel_continuous
  have hi : IntegrableOn (fun v : ℝ => t*weightedMajorKernel (t*v)) (Ioi (0 : ℝ)) :=
    ((weightedMajorKernel_integrable.comp_mul_left' ht.ne').const_mul t).integrableOn
  apply (hi.mul_const (|H|/Real.pi)).mono'
  · have hm : Measurable (fun v : ℝ => t*weightedMajorKernel (t*v)*bandKernel H v⁻¹) := by
      unfold bandKernel
      fun_prop
    exact hm.aestronglyMeasurable
  · exact Eventually.of_forall (fun v => by
      rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg
        (mul_nonneg ht.le (weightedMajorKernel_nonneg _))]
      exact mul_le_mul_of_nonneg_left (bandKernel_abs_le H v⁻¹)
        (mul_nonneg ht.le (weightedMajorKernel_nonneg _)))

lemma bandLimitedMajorKernel_integrable (H t : ℝ) (ht : 0 < t) :
    IntegrableOn (fun w : ℝ => majorKernel (t/w)*bandKernel H w/w) (Ioi (0 : ℝ)) := by
  apply (integrable_mellin_inverse (fun w => majorKernel (t/w)*bandKernel H w)).mpr
  apply (inverse_major_integrable H t ht).congr_fun _ measurableSet_Ioi
  intro v hv
  exact (inverse_major_integrand H t v hv).symm

lemma bandLimitedMajorKernel_inverse (H t : ℝ) :
    bandLimitedMajorKernel H t =
      ∫ v in Ioi (0 : ℝ), t*weightedMajorKernel (t*v)*bandKernel H v⁻¹ := by
  unfold bandLimitedMajorKernel mellinConv
  rw [integral_mellin_inverse (fun w => majorKernel (t/w)*bandKernel H w)]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro v hv
  exact inverse_major_integrand H t v hv

private lemma bandLimitedMajorKernel_abs_le_pos (H t : ℝ) (ht : 0 < t) :
    |bandLimitedMajorKernel H t| ≤ (|H|/Real.pi)*(∫ v in Ioi (0 : ℝ), weightedMajorKernel v) := by
  rw [bandLimitedMajorKernel_inverse]
  have hi : IntegrableOn (fun v : ℝ => t*weightedMajorKernel (t*v)) (Ioi (0 : ℝ)) :=
    ((weightedMajorKernel_integrable.comp_mul_left' ht.ne').const_mul t).integrableOn
  have hn : |∫ v in Ioi (0 : ℝ), t*weightedMajorKernel (t*v)*bandKernel H v⁻¹| ≤
      ∫ v in Ioi (0 : ℝ), (|H|/Real.pi)*(t*weightedMajorKernel (t*v)) := by
    rw [← Real.norm_eq_abs]
    apply (norm_integral_le_integral_norm _).trans
    apply integral_mono (inverse_major_integrable H t ht).norm (hi.const_mul (|H|/Real.pi))
    intro v
    dsimp only
    rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (mul_nonneg ht.le (weightedMajorKernel_nonneg _))]
    convert! mul_le_mul_of_nonneg_left (bandKernel_abs_le H v⁻¹)
      (mul_nonneg ht.le (weightedMajorKernel_nonneg _)) using 1 <;> ring
  refine hn.trans_eq ?_
  rw [integral_const_mul,integral_const_mul,integral_comp_mul_left_Ioi weightedMajorKernel 0 ht]
  simp only [mul_zero,smul_eq_mul]
  field_simp

lemma majorKernel_zero_of_nonpos (t : ℝ) (ht : t ≤ 0) : majorKernel t = 0 := by
  by_cases hz : t = 0
  · subst t; simp [majorKernel]
  · have hn : t ∉ Icc (0 : ℝ) 2 := by intro h; exact hz (le_antisymm ht h.1)
    simp [majorKernel,hn]

lemma bandLimitedMajorKernel_zero_of_nonpos (H t : ℝ) (ht : t ≤ 0) :
    bandLimitedMajorKernel H t = 0 := by
  unfold bandLimitedMajorKernel mellinConv
  apply integral_eq_zero_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with w hw
  rw [majorKernel_zero_of_nonpos (t/w) (div_nonpos_of_nonpos_of_nonneg ht hw.le)]
  simp

theorem etaPlus_gaussian_envelope :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, |etaPlus t| ≤ C*|t| *Real.exp (-(t^2)/2) := by
  let C : ℝ := ((200 : ℝ)/Real.pi)*(∫ v in Ioi (0 : ℝ), weightedMajorKernel v)
  have hC : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg (by positivity) (integral_nonneg weightedMajorKernel_nonneg)
  refine ⟨C,hC,?_⟩
  intro t
  have hb : |bandLimitedMajorKernel 200 t| ≤ C := by
    by_cases ht : 0 < t
    · simpa only [abs_of_pos (by norm_num : (0 : ℝ) < 200)] using
        bandLimitedMajorKernel_abs_le_pos 200 t ht
    · rw [bandLimitedMajorKernel_zero_of_nonpos 200 t (le_of_not_gt ht),abs_zero]
      exact hC
  unfold etaPlus
  rw [abs_mul,abs_mul,abs_of_pos (Real.exp_pos _)]
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hb (abs_nonneg t)) (Real.exp_pos _).le

end Helfgott

namespace Helfgott

lemma vonMangoldt_le_nat (n : ℕ) : ArithmeticFunction.vonMangoldt n ≤ (n : ℝ) := by
  by_cases hn : n = 0
  · subst n; simp
  · have hp : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hl := Real.log_le_sub_one_of_pos hp
    exact ArithmeticFunction.vonMangoldt_le_log.trans (by linarith)


end Helfgott

namespace Helfgott

theorem etaPlus_vonMangoldt_summable (x : ℝ) (hx : 0 < x) :
    Summable (fun n : ℕ => ArithmeticFunction.vonMangoldt n * etaPlus ((n : ℝ)/x)) := by
  obtain ⟨C,hC,hbound⟩ := etaPlus_gaussian_envelope
  let r : ℝ := 1/(2*x^2)
  have hr : 0 < r := by dsimp [r]; positivity
  have hg : Summable (fun n : ℕ => (C/x)*((n : ℝ)^2*Real.exp (-r*n))) :=
    (Real.summable_pow_mul_exp_neg_nat_mul 2 hr).mul_left (C/x)
  apply hg.of_norm_bounded
  intro n
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hn2 : (n : ℝ) ≤ (n : ℝ)^2 := by
    have h : (n : ℝ) ≤ (n : ℝ)*(n : ℝ) := by exact_mod_cast Nat.le_mul_self n
    nlinarith
  have he : Real.exp (-r*(n : ℝ)^2) ≤ Real.exp (-r*n) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have ht : |etaPlus ((n : ℝ)/x)| ≤ (C/x)*(n : ℝ)*Real.exp (-r*(n : ℝ)^2) := by
    apply (hbound ((n : ℝ)/x)).trans_eq
    rw [abs_of_nonneg (div_nonneg hn hx.le)]
    have heq : -(((n : ℝ)/x)^2)/2 = -r*(n : ℝ)^2 := by dsimp [r]; ring
    rw [heq]
    ring
  rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
  calc
    ArithmeticFunction.vonMangoldt n * |etaPlus ((n : ℝ)/x)| ≤
      (n : ℝ)*|etaPlus ((n : ℝ)/x)| :=
        mul_le_mul_of_nonneg_right (vonMangoldt_le_nat n) (abs_nonneg _)
    _ ≤ (n : ℝ)*((C/x)*(n : ℝ)*Real.exp (-r*(n : ℝ)^2)) :=
      mul_le_mul_of_nonneg_left ht hn
    _ ≤ (n : ℝ)*((C/x)*(n : ℝ)*Real.exp (-r*n)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left he
        (mul_nonneg (div_nonneg hC hx.le) hn)) hn
    _ = (C/x)*((n : ℝ)^2*Real.exp (-r*n)) := by ring

lemma etaPlus_vonMangoldt_complex_summable (x : ℝ) (hx : 0 < x) :
    Summable (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ)*
      (etaPlus ((n : ℝ)/x) : ℂ)) := by
  have h := Complex.summable_ofReal.mpr (etaPlus_vonMangoldt_summable x hx)
  simpa only [Complex.ofReal_mul] using h

end Helfgott

theorem solution (x : ℝ) (hx : 0 < x) :
    Summable (fun n : ℕ => ArithmeticFunction.vonMangoldt n * Helfgott.etaPlus ((n : ℝ)/x)) :=
  Helfgott.etaPlus_vonMangoldt_summable x hx

#print axioms solution
