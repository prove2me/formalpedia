-- Prove2me | solution 1 for JewellMRP.Discounted.qtilde_mem_Ico
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-28T00:19:07.211984+00:00
-- url     : https://prove2.me/submissions/f7e49d9e-6b30-410b-895a-1a2f04ca3c1c

import Mathlib
import Definitions.Def_JewellMRP_Discounted_MRP

open MeasureTheory
open JewellMRP.Discounted

private theorem exp_int_bounds (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : μ (Set.Iic (0 : ℝ)) = 0) {s : ℝ} (hs : 0 < s) :
    0 ≤ (∫ t in Set.Ioi (0 : ℝ), Real.exp (-(s * t)) ∂μ) ∧
      (∫ t in Set.Ioi (0 : ℝ), Real.exp (-(s * t)) ∂μ) < 1 := by
  have hIoi : μ (Set.Ioi (0 : ℝ)) = 1 := by
    have hcompl : Set.Ioi (0 : ℝ) = (Set.Iic (0 : ℝ))ᶜ := by ext x; simp
    rw [hcompl, measure_compl measurableSet_Iic (measure_ne_top _ _), hμ, measure_univ,
      tsub_zero]
  haveI hprob : IsProbabilityMeasure (μ.restrict (Set.Ioi (0 : ℝ))) := by
    constructor
    rw [Measure.restrict_apply_univ]
    exact hIoi
  have hmeas : Measurable (fun t : ℝ => Real.exp (-(s * t))) := by fun_prop
  have hle1 : ∀ t : ℝ, 0 < t → Real.exp (-(s * t)) ≤ 1 := by
    intro t ht
    have hneg : -(s * t) ≤ 0 := by nlinarith
    calc Real.exp (-(s * t)) ≤ Real.exp 0 := Real.exp_le_exp.mpr hneg
      _ = 1 := Real.exp_zero
  have hint : Integrable (fun t : ℝ => Real.exp (-(s * t)))
      (μ.restrict (Set.Ioi (0 : ℝ))) := by
    refine Integrable.mono' (integrable_const 1) hmeas.aestronglyMeasurable ?_
    rw [ae_restrict_iff' measurableSet_Ioi]
    filter_upwards with t ht
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact hle1 t (Set.mem_Ioi.mp ht)
  have hnn : 0 ≤ (∫ t in Set.Ioi (0 : ℝ), Real.exp (-(s * t)) ∂μ) :=
    integral_nonneg fun t => (Real.exp_pos _).le
  refine ⟨hnn, ?_⟩
  have hfnn : ∀ᵐ t ∂(μ.restrict (Set.Ioi (0 : ℝ))), (0 : ℝ) ≤ 1 - Real.exp (-(s * t)) := by
    rw [ae_restrict_iff' measurableSet_Ioi]
    filter_upwards with t ht
    have := hle1 t (Set.mem_Ioi.mp ht)
    linarith
  have hint2 : Integrable (fun t : ℝ => 1 - Real.exp (-(s * t)))
      (μ.restrict (Set.Ioi (0 : ℝ))) := (integrable_const 1).sub hint
  have hsupp : 0 < (μ.restrict (Set.Ioi (0 : ℝ)))
      (Function.support fun t : ℝ => 1 - Real.exp (-(s * t))) := by
    have hsub : Set.Ioi (0 : ℝ)
        ⊆ Function.support fun t : ℝ => 1 - Real.exp (-(s * t)) := by
      intro t ht
      have ht0 : 0 < t := Set.mem_Ioi.mp ht
      have hlt : Real.exp (-(s * t)) < 1 := by
        have hneg : -(s * t) < 0 := by nlinarith
        calc Real.exp (-(s * t)) < Real.exp 0 := Real.exp_lt_exp.mpr hneg
          _ = 1 := Real.exp_zero
      simp only [Function.mem_support, ne_eq]
      intro hc
      linarith
    have hmono := measure_mono (μ := μ.restrict (Set.Ioi (0 : ℝ))) hsub
    have hν0 : (μ.restrict (Set.Ioi (0 : ℝ))) (Set.Ioi (0 : ℝ)) = 1 := by
      rw [Measure.restrict_apply measurableSet_Ioi, Set.inter_self]
      exact hIoi
    rw [hν0] at hmono
    exact lt_of_lt_of_le zero_lt_one hmono
  have hpos : 0 < ∫ t in Set.Ioi (0 : ℝ), (1 - Real.exp (-(s * t))) ∂μ :=
    (integral_pos_iff_support_of_nonneg_ae hfnn hint2).mpr hsupp
  have hsplit : (∫ t in Set.Ioi (0 : ℝ), (1 - Real.exp (-(s * t))) ∂μ)
      = 1 - ∫ t in Set.Ioi (0 : ℝ), Real.exp (-(s * t)) ∂μ := by
    rw [integral_sub (integrable_const 1) hint]
    simp
  rw [hsplit] at hpos
  linarith

private theorem ftilde_bounds {S A : Type*} [Fintype S] (M : MRP S A) {s : ℝ} (hs : 0 < s)
    (z : A) (i j : S) : 0 ≤ ftilde M z i j s ∧ ftilde M z i j s < 1 := by
  haveI := M.F_prob z i j
  exact exp_int_bounds (M.F z i j) (M.F_Iic_zero z i j) hs

private theorem qtilde_bounds {S A : Type*} [Fintype S] (M : MRP S A) {s : ℝ} (hs : 0 < s)
    (z : A) (i j : S) : 0 ≤ qtilde M s z i j ∧ qtilde M s z i j < 1 := by
  obtain ⟨hf0, hf1⟩ := ftilde_bounds M hs z i j
  have hp0 : 0 ≤ M.p z i j := M.p_nonneg z i j
  have hp1 : M.p z i j ≤ 1 := by
    have := Finset.single_le_sum (f := fun k => M.p z i k)
      (fun k _ => M.p_nonneg z i k) (Finset.mem_univ j)
    rw [M.p_sum z i] at this
    exact this
  refine ⟨mul_nonneg hp0 hf0, ?_⟩
  calc M.p z i j * ftilde M z i j s ≤ 1 * ftilde M z i j s := by
        exact mul_le_mul_of_nonneg_right hp1 hf0
    _ = ftilde M z i j s := one_mul _
    _ < 1 := hf1

theorem solution {S A : Type*} [Fintype S] (M : MRP S A) {s : ℝ} (hs : 0 < s)
    (z : A) (i j : S) : qtilde M s z i j ∈ Set.Ico 0 1 := by
  obtain ⟨h0, h1⟩ := qtilde_bounds M hs z i j
  exact Set.mem_Ico.mpr ⟨h0, h1⟩
