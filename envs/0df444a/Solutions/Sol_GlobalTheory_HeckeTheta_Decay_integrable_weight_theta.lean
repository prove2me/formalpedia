-- Prove2me | solution 1 for GlobalTheory.HeckeTheta.Decay.integrable_weight_theta
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:31:12.199654+00:00
-- url     : https://prove2.me/submissions/a14e8367-abab-431a-9a70-85a01a2e5b0f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_CompletedLStripBounds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormWt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaussZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegrableWeightedHeckeThetaKernelHalfSpace
import Theorems.Thm_GlobalTheory_HeckeTheta_Decay_gC_nonneg
import Theorems.Thm_GlobalTheory_HeckeTheta_Decay_norm_term_le
import Theorems.Thm_GlobalTheory_HeckeTheta_Decay_continuous_theta
import Theorems.Thm_GlobalTheory_HeckeTheta_Decay_one_dim
import Theorems.Thm_GlobalTheory_HeckeTheta_Decay_integrable_exp_neg_abs_one
import Theorems.Thm_GlobalTheory_CMVal_coe_latticeSub
import Theorems.Thm_GlobalTheory_HeckeTheta_gauss_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMVal.coe_latticeSub



set_option autoImplicit false
open NumberField MeasureTheory
noncomputable section
open GlobalTheory GlobalTheory.HeckeTheta GlobalTheory.HeckeTheta.Decay
open GlobalTheory.HeckeTheta
namespace GlobalTheory.HeckeTheta.Decay
theorem _root_.solution : ∀ (I : Type) [Fintype I] {ι : Type} (e : ι → I → ℂ) (a : ι → ℂ) (n : I → ℤ) (q : (I → ℝ) → ℝ) (B R : ℝ), (∃ i, n i ≠ 0) → (∀ ε : ℝ, 0 < ε → Summable (fun j => ‖a j‖ * Real.exp (-ε * ‖e j‖ ^ 2))) → (∃ δ : ℝ, 0 < δ ∧ ∀ j, a j ≠ 0 → e j ≠ 0 → δ ≤ ‖e j‖) → Measurable q → (∀ y, |q y| ≤ B) → (∀ y, q y ≠ 0 → ∀ i j, y i - y j ≤ R) → MeasureTheory.AEStronglyMeasurable (fun y => (q y : ℂ) * GlobalTheory.HeckeTheta.theta e a n y) MeasureTheory.volume ∧ ∀ σ : ℝ, MeasureTheory.Integrable (fun y => ‖(q y : ℂ) * GlobalTheory.HeckeTheta.theta e a n y‖ * Real.exp (σ * ∑ i, y i)) (MeasureTheory.volume.restrict {y : I → ℝ | 0 ≤ ∑ i, y i}) := by
  intro I _ ι e a n q B R hn ha hδ hq hqB hqR
  obtain ⟨δ, hδ0, hδ⟩ := hδ
  obtain ⟨i0, hi0⟩ := hn
  haveI : Nonempty I := ⟨i0⟩
  have hcont := continuous_theta e a n ha
  have hmeas : AEStronglyMeasurable (fun y => (q y : ℂ) * theta e a n y) volume :=
    ((Complex.measurable_ofReal.comp hq).mul hcont.measurable).aestronglyMeasurable
  refine ⟨hmeas, fun σ => ?_⟩
  have hB : 0 ≤ B := (abs_nonneg _).trans (hqB 0)
  set R' := max R 0 with hR'
  have hR0 : 0 ≤ R' := le_max_right _ _
  have hqR' : ∀ y, q y ≠ 0 → ∀ i j, y i ≤ y j + R' := fun y hy i j => by
    have := hqR y hy i j; have := le_max_left R 0; linarith
  set N : ℝ := (Fintype.card I : ℝ) with hN
  have hN0 : 0 < N := by rw [hN]; exact_mod_cast Fintype.card_pos
  set τ0 : ℝ := Real.exp (-R') / N with hτ0
  have hτ0p : 0 < τ0 := by positivity
  set ε0 : ℝ := Real.pi / 2 * τ0 with hε0
  have hε0p : 0 < ε0 := by positivity
  have hS := ha ε0 hε0p
  set S : ℝ := ∑' j, ‖a j‖ * Real.exp (-ε0 * ‖e j‖ ^ 2) with hSdef
  have hS0 : 0 ≤ S := tsum_nonneg fun j => by positivity
  set c' : ℝ := Real.pi / 2 * δ ^ 2 * τ0 with hc'
  have hc'p : 0 < c' := by positivity
  set K : ℝ := (|σ| + 1) ^ 2 / (2 * c') + (|σ| + 1) * R' with hK
  set G : (I → ℝ) → ℝ := fun y => B * gC n * S * ∏ i, (Real.exp K * Real.exp (-1 * |y i|)) with hG

  have htheta : ∀ y, q y ≠ 0 → 0 ≤ ∑ i, y i →
      ‖theta e a n y‖ ≤ gC n * Real.exp (-c' * ∑ i, Real.exp (y i)) * S := by
    intro y hy hs
    obtain ⟨k, hk⟩ : ∃ k, 0 ≤ y k := by
      by_contra h
      push_neg at h
      have := Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun i (_ : i ∈ Finset.univ) => h i)
      simp only [Finset.sum_const_zero] at this
      linarith
    set T : ℝ := Real.exp (-R') * (∑ i, Real.exp (y i)) / N with hT
    have hTi : ∀ i, T ≤ Real.exp (y i) := by
      intro i
      rw [hT, div_le_iff₀ hN0]
      have h1 : ∀ j, Real.exp (-R') * Real.exp (y j) ≤ Real.exp (y i) := fun j => by
        rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by have := hqR' y hy j i; linarith)
      calc Real.exp (-R') * ∑ j, Real.exp (y j) = ∑ j, Real.exp (-R') * Real.exp (y j) := Finset.mul_sum _ _ _
        _ ≤ ∑ _j : I, Real.exp (y i) := Finset.sum_le_sum fun j _ => h1 j
        _ = Real.exp (y i) * N := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hN, mul_comm]
    have hTτ : τ0 ≤ T := by
      rw [hT, hτ0]
      apply div_le_div_of_nonneg_right _ hN0.le
      have h1 : 1 ≤ ∑ i, Real.exp (y i) :=
        (Real.one_le_exp hk).trans (Finset.single_le_sum (f := fun i => Real.exp (y i))
          (fun i _ => (Real.exp_pos _).le) (Finset.mem_univ k))
      have := Real.exp_pos (-R')
      nlinarith
    have hT0 : 0 ≤ T := hτ0p.le.trans hTτ
    have hterm : ∀ j, ‖a j * gauss n (dil y (e j))‖ ≤
        gC n * Real.exp (-c' * ∑ i, Real.exp (y i)) * (‖a j‖ * Real.exp (-ε0 * ‖e j‖ ^ 2)) := by
      intro j
      have hC := gC_nonneg n
      by_cases haj : a j = 0
      · simp only [haj, zero_mul, norm_zero, mul_zero]; exact le_refl _
      by_cases hej : e j = 0
      · have : dil y (e j) = 0 := by funext i; simp [dil, hej]
        rw [this, gauss_zero ⟨i0, hi0⟩, mul_zero, norm_zero]
        positivity
      have hd := hδ j haj hej
      rw [norm_mul]
      have h1 := norm_term_le n y (e j) hT0 hTi
      have h2 : Real.exp (-Real.pi * T * ‖e j‖ ^ 2) ≤
          Real.exp (-c' * ∑ i, Real.exp (y i)) * Real.exp (-ε0 * ‖e j‖ ^ 2) := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        have e1 : c' * ∑ i, Real.exp (y i) = Real.pi / 2 * δ ^ 2 * T := by
          rw [hc', hT, hτ0]; field_simp
        rw [hε0]
        have hδe : δ ^ 2 ≤ ‖e j‖ ^ 2 := pow_le_pow_left₀ hδ0.le hd 2
        have a1 := mul_le_mul_of_nonneg_left hδe hT0
        have a2 := mul_le_mul_of_nonneg_right hTτ (sq_nonneg ‖e j‖)
        have hp := Real.pi_pos
        nlinarith [mul_le_mul_of_nonneg_left a1 hp.le, mul_le_mul_of_nonneg_left a2 hp.le, e1]
      calc ‖a j‖ * ‖gauss n (dil y (e j))‖ ≤ ‖a j‖ * (gC n * Real.exp (-Real.pi * T * ‖e j‖ ^ 2)) :=
            mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
        _ ≤ ‖a j‖ * (gC n * (Real.exp (-c' * ∑ i, Real.exp (y i)) * Real.exp (-ε0 * ‖e j‖ ^ 2))) := by
            gcongr
        _ = _ := by ring
    have hsum : HasSum (fun j => gC n * Real.exp (-c' * ∑ i, Real.exp (y i)) *
        (‖a j‖ * Real.exp (-ε0 * ‖e j‖ ^ 2))) (gC n * Real.exp (-c' * ∑ i, Real.exp (y i)) * S) :=
      hS.hasSum.mul_left _
    exact tsum_of_norm_bounded hsum hterm
  have hbound : ∀ y, 0 ≤ ∑ i, y i →
      ‖(q y : ℂ) * theta e a n y‖ * Real.exp (σ * ∑ i, y i) ≤ G y := by
    intro y hs
    have hG0 : 0 ≤ G y := by
      simp only [hG]
      have := gC_nonneg n
      positivity
    by_cases hq0 : q y = 0
    · simp only [hq0, Complex.ofReal_zero, zero_mul, norm_zero]; exact hG0
    have hyR : ∀ i, -R' ≤ y i := by
      obtain ⟨k, hk⟩ : ∃ k, 0 ≤ y k := by
        by_contra h
        push_neg at h
        have := Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun i (_ : i ∈ Finset.univ) => h i)
        simp only [Finset.sum_const_zero] at this
        linarith
      intro i; have := hqR' y hq0 k i; linarith
    have h1 := htheta y hq0 hs
    have h2 : Real.exp (-c' * ∑ i, Real.exp (y i)) * Real.exp (σ * ∑ i, y i) ≤
        ∏ i, (Real.exp K * Real.exp (-1 * |y i|)) := by
      rw [← Real.exp_add]
      have e1 : -c' * ∑ i, Real.exp (y i) + σ * ∑ i, y i = ∑ i, (σ * y i - c' * Real.exp (y i)) := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun i _ => by ring
      rw [e1, Real.exp_sum]
      apply Finset.prod_le_prod (fun i _ => (Real.exp_pos _).le)
      intro i _
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have := one_dim (σ := σ) hc'p hR0 (hyR i)
      rw [hK]; linarith
    have hqy : ‖(q y : ℂ)‖ ≤ B := by rw [Complex.norm_real, Real.norm_eq_abs]; exact hqB y
    rw [norm_mul]
    have hC := gC_nonneg n
    calc ‖(q y : ℂ)‖ * ‖theta e a n y‖ * Real.exp (σ * ∑ i, y i)
        ≤ B * (gC n * Real.exp (-c' * ∑ i, Real.exp (y i)) * S) * Real.exp (σ * ∑ i, y i) := by
          gcongr
      _ = B * gC n * S * (Real.exp (-c' * ∑ i, Real.exp (y i)) * Real.exp (σ * ∑ i, y i)) := by ring
      _ ≤ B * gC n * S * ∏ i, (Real.exp K * Real.exp (-1 * |y i|)) := by
          gcongr
  have hGi : Integrable G volume := by
    have h1 : Integrable (fun y : I → ℝ => ∏ i, (Real.exp K * Real.exp (-1 * |y i|))) volume :=
      Integrable.fintype_prod (f := fun _ x => Real.exp K * Real.exp (-1 * |x|))
        fun _ => integrable_exp_neg_abs_one.const_mul _
    exact h1.const_mul _
  have hset : MeasurableSet {y : I → ℝ | 0 ≤ ∑ i, y i} :=
    measurableSet_le measurable_const (by fun_prop)
  refine Integrable.mono' hGi.restrict ?_ ?_
  · exact (hmeas.norm.mul (Continuous.aestronglyMeasurable (by fun_prop))).restrict
  · rw [ae_restrict_iff' hset]
    filter_upwards with y hy
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hbound y hy
end GlobalTheory.HeckeTheta.Decay
