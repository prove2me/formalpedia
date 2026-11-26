-- Prove2me | solution 1 for Malliavin.integral_restrict_frame_eq_zero_of_rectangles
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:32:36.328503+00:00
-- url     : https://prove2.me/submissions/17396525-9109-4faf-911c-57e503e58e1d

import Definitions.Def_Malliavin_ClarkOcone
import Definitions.Def_Malliavin_PredictableDensity
import Theorems.Thm_Malliavin_isPiSystem_predictableRectangle
import Theorems.Thm_Malliavin_generateFrom_predictableRectangle
import Theorems.Thm_Malliavin_CameronMartin_covarianceMap_apply
import Theorems.Thm_Malliavin_CameronMartin_densityExponent_zero
import Theorems.Thm_Malliavin_CameronMartin_density_toReal
import Theorems.Thm_Malliavin_CameronMartin_density_zero
import Theorems.Thm_Malliavin_CameronMartin_expectationMap_apply
import Theorems.Thm_Malliavin_CameronMartin_inclusion_apply
import Theorems.Thm_Malliavin_CameronMartin_realDensity_zero
import Theorems.Thm_Malliavin_CameronMartin_translated_zero
import Theorems.Thm_Malliavin_mem_symmetricSubmodule
attribute [local simp] Malliavin.CameronMartin.covarianceMap_apply
attribute [local simp] Malliavin.CameronMartin.densityExponent_zero
attribute [local simp] Malliavin.CameronMartin.density_toReal
attribute [local simp] Malliavin.CameronMartin.density_zero
attribute [local simp] Malliavin.CameronMartin.expectationMap_apply
attribute [local simp] Malliavin.CameronMartin.inclusion_apply
attribute [local simp] Malliavin.CameronMartin.realDensity_zero
attribute [local simp] Malliavin.CameronMartin.translated_zero
attribute [local simp] Malliavin.mem_symmetricSubmodule



set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Function
open scoped ENNReal NNReal InnerProductSpace
universe u_1 u_2 u_3 u_4 u_5
noncomputable section
open Malliavin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
omit [CompleteSpace W] [BorelSpace W]
namespace Malliavin
theorem _root_.solution
    (𝓕 : Filtration ℝ≥0 (inferInstance : MeasurableSpace W))
    (g : PredictableProcessL2 𝓕 P)
    (hrect : ∀ R ∈ predictableRectangle 𝓕,
      ∫ z in R, (g : ℝ≥0 × W → ℝ) z
        ∂nonnegativeLebesgueMeasure.prod P = 0)
    (n : ℕ) (s : Set (ℝ≥0 × W)) (hs : MeasurableSet[𝓕.predictable] s) :
    ∫ z in s, (g : ℝ≥0 × W → ℝ) z
      ∂(nonnegativeLebesgueMeasure.prod P).restrict
        (Set.Ioc 0 ((n : ℝ≥0) + 1) ×ˢ Set.univ) = 0 := by
  let μ₀ := nonnegativeLebesgueMeasure.prod P
  let Φ : Set (ℝ≥0 × W) := Set.Ioc 0 ((n : ℝ≥0) + 1) ×ˢ Set.univ
  have hΦmem : Φ ∈ predictableRectangle 𝓕 :=
    Or.inr ⟨0, (n : ℝ≥0) + 1, Set.univ, by positivity,
      MeasurableSet.univ, rfl⟩
  have hRpred : ∀ R ∈ predictableRectangle 𝓕,
      MeasurableSet[𝓕.predictable] R := by
    intro R hR
    rw [← generateFrom_predictableRectangle 𝓕]
    exact MeasurableSpace.measurableSet_generateFrom hR
  have hμΦ : μ₀ Φ ≠ ∞ := by
    rw [Measure.prod_prod]
    exact ENNReal.mul_ne_top
      (nonnegativeLebesgueMeasure_Ioc_ne_top 0 ((n : ℝ≥0) + 1))
      (measure_ne_top P Set.univ)
  have hint : Integrable (g : ℝ≥0 × W → ℝ) (μ₀.restrict Φ) :=
    integrableOn_Lp_of_measure_ne_top (g : TimeProcessL2 P) one_le_two hμΦ
  have htotal : ∫ z, (g : ℝ≥0 × W → ℝ) z ∂μ₀.restrict Φ = 0 :=
    hrect Φ hΦmem
  have hbasic : ∀ R ∈ predictableRectangle 𝓕,
      ∫ z in R, (g : ℝ≥0 × W → ℝ) z ∂μ₀.restrict Φ = 0 := by
    intro R hR
    have heq : ∫ z in R, (g : ℝ≥0 × W → ℝ) z ∂μ₀.restrict Φ =
        ∫ z in R ∩ Φ, (g : ℝ≥0 × W → ℝ) z ∂μ₀ := by
      rw [show ∫ z in R, (g : ℝ≥0 × W → ℝ) z ∂μ₀.restrict Φ =
          ∫ z, (g : ℝ≥0 × W → ℝ) z ∂((μ₀.restrict Φ).restrict R) from rfl,
        Measure.restrict_restrict (predictable_le_prod 𝓕 R (hRpred R hR))]
    rw [heq]
    by_cases hne : (R ∩ Φ).Nonempty
    · exact hrect _ (isPiSystem_predictableRectangle 𝓕 R hR Φ hΦmem hne)
    · rw [Set.not_nonempty_iff_eq_empty.mp hne, setIntegral_empty]
  refine MeasurableSpace.induction_on_inter
    (C := fun s _ ↦ ∫ z in s, (g : ℝ≥0 × W → ℝ) z ∂μ₀.restrict Φ = 0)
    (h_eq := (generateFrom_predictableRectangle 𝓕).symm)
    (h_inter := isPiSystem_predictableRectangle 𝓕)
    (empty := setIntegral_empty)
    (basic := hbasic)
    (compl := ?_) (iUnion := ?_) s hs
  · intro S hS hzero
    have hsplit := integral_add_compl
      (μ := μ₀.restrict Φ) (f := (g : ℝ≥0 × W → ℝ))
      (predictable_le_prod 𝓕 S hS) hint
    linarith
  · intro f hf hfm hzero
    rw [integral_iUnion (fun i ↦ predictable_le_prod 𝓕 (f i) (hfm i))
      hf hint.integrableOn]
    simp only [hzero, tsum_zero]
end Malliavin
