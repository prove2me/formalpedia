-- Prove2me | solution 1 for LevyStochCalc.Brownian.Ito.offDiagonal_increment_integral_zero_weighted_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:18:11.348267+00:00
-- url     : https://prove2.me/submissions/1b62ef93-0b7e-4081-991c-1811841f3de4

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoL2CompletionCompensator

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoL2CompletionCompensator.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory
open scoped NNReal ENNReal
universe u
variable {Ω : Type u} [MeasurableSpace Ω]
/-- `∫ (W_b − W_a) = 0` for `0 ≤ a < b`. -/
lemma LevyStochCalc.Brownian.Ito.brownian_incr_mean
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P) {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    ∫ ω, (W.W b ω - W.W a ω) ∂P = 0 := by
  have h_meas : Measurable (fun ω => W.W b ω - W.W a ω) :=
    (W.measurable_eval b).sub (W.measurable_eval a)
  rw [show (∫ ω, (W.W b ω - W.W a ω) ∂P)
        = ∫ x : ℝ, x ∂(P.map (fun ω => W.W b ω - W.W a ω)) from
      (MeasureTheory.integral_map h_meas.aemeasurable
        (by fun_prop : MeasureTheory.AEStronglyMeasurable (fun x : ℝ => x) _)).symm,
    W.increment_gaussian ha hab]
  exact ProbabilityTheory.integral_id_gaussianReal
/-- **Weighted off-diagonal vanishing.** For two increments with the second
strictly after the first (`a₁ < b₁ ≤ a₂ < b₂`), `Fᵢ`-measurable coefficients, and
a bounded `F_{a₁}`-measurable weight `g`,
`∫ g · (ξ₁·ΔW₁)·(ξ₂·ΔW₂) = 0`. The weighted analogue of
`offDiagonal_increment_integral_zero`: `f := g·ξ₁·ΔW₁·ξ₂` is `F_{a₂}`-measurable
and `ΔW₂ ⟂ F_{a₂}` is centred, so `𝔼[f·ΔW₂] = 𝔼[f]·0 = 0`. With `g = 1_B`
(`B ∈ F_s`, `s ≤ a₁`) this gives the off-diagonal of the set-level Itô isometry. -/
lemma solution
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : LevyStochCalc.Brownian.IsBrownianFiltration W ℱ)
    {a₁ b₁ a₂ b₂ : ℝ} (ha₁ : 0 ≤ a₁) (h₁ : a₁ < b₁) (h₁₂ : b₁ ≤ a₂) (h₂ : a₂ < b₂)
    (ξ₁ ξ₂ g : Ω → ℝ)
    (hadapt₁ : @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ a₁) ξ₁)
    (hadapt₂ : @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ a₂) ξ₂)
    (hg : @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ a₁) g) :
    ∫ ω, g ω * ((ξ₁ ω * (W.W b₁ ω - W.W a₁ ω)) * (ξ₂ ω * (W.W b₂ ω - W.W a₂ ω))) ∂P
      = 0 := by
  set ΔW₂ : Ω → ℝ := fun ω => W.W b₂ ω - W.W a₂ ω with hΔW₂_def
  have ha₂_nn : 0 ≤ a₂ := le_trans ha₁ (le_trans (le_of_lt h₁) h₁₂)
  have ha₁a₂ : a₁ ≤ a₂ := le_trans (le_of_lt h₁) h₁₂
  have hξ₁meas : Measurable ξ₁ :=
    (hadapt₁.mono (ℱ.le a₁)).measurable
  have hξ₂meas : Measurable ξ₂ :=
    (hadapt₂.mono (ℱ.le a₂)).measurable
  have hgmeas : Measurable g :=
    (hg.mono (ℱ.le a₁)).measurable
  set f : Ω → ℝ := fun ω => g ω * (ξ₁ ω * (W.W b₁ ω - W.W a₁ ω)) * ξ₂ ω with hf_def
  rw [show (fun ω => g ω * ((ξ₁ ω * (W.W b₁ ω - W.W a₁ ω)) * (ξ₂ ω * ΔW₂ ω)))
        = fun ω => f ω * ΔW₂ ω from by funext ω; simp only [hf_def]; ring]
  have h_Wb₁_meas : @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ a₂) (W.W b₁) :=
    ((hℱ.measurable b₁).stronglyMeasurable).mono
      (ℱ.mono h₁₂)
  have h_Wa₁_meas : @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ a₂) (W.W a₁) :=
    ((hℱ.measurable a₁).stronglyMeasurable).mono
      (ℱ.mono
        (le_trans (le_of_lt h₁) h₁₂))
  have h_ξ₁_F_meas : @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ a₂) ξ₁ :=
    hadapt₁.mono (ℱ.mono ha₁a₂)
  have h_g_F_meas : @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ a₂) g :=
    hg.mono (ℱ.mono ha₁a₂)
  have h_f_F_meas : @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ a₂) f :=
    (h_g_F_meas.mul (h_ξ₁_F_meas.mul (h_Wb₁_meas.sub h_Wa₁_meas))).mul hadapt₂
  have h_indep_F_ΔW₂ := hℱ.indep ha₂_nn h₂
  have h_f_meas : Measurable f :=
    (hgmeas.mul (hξ₁meas.mul ((W.measurable_eval b₁).sub (W.measurable_eval a₁)))).mul hξ₂meas
  have h_ΔW₂_meas : Measurable ΔW₂ := (W.measurable_eval b₂).sub (W.measurable_eval a₂)
  have h_f_comap_le : MeasurableSpace.comap f inferInstance ≤ ℱ a₂ :=
    h_f_F_meas.measurable.comap_le
  have h_indep_f_ΔW₂ : ProbabilityTheory.IndepFun f ΔW₂ P := by
    rw [ProbabilityTheory.IndepFun_iff]
    intro u v hu hv
    rw [ProbabilityTheory.Indep_iff] at h_indep_F_ΔW₂
    exact h_indep_F_ΔW₂ u v (h_f_comap_le u hu) hv
  have h_ΔW₂_mean : ∫ ω, ΔW₂ ω ∂P = 0 := LevyStochCalc.Brownian.Ito.brownian_incr_mean W ha₂_nn h₂
  rw [show (fun ω => f ω * ΔW₂ ω) = f * ΔW₂ from rfl,
    h_indep_f_ΔW₂.integral_mul_eq_mul_integral h_f_meas.aestronglyMeasurable
    h_ΔW₂_meas.aestronglyMeasurable, h_ΔW₂_mean, mul_zero]
