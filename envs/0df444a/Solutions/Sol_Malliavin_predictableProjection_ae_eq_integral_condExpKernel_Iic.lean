-- Prove2me | solution 1 for Malliavin.predictableProjection_ae_eq_integral_condExpKernel_Iic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:32:57.141479+00:00
-- url     : https://prove2.me/submissions/b5a8ad17-3c87-42f5-99ae-29316334dc84

import Definitions.Def_Malliavin_ClarkOcone
import Mathlib.Probability.Kernel.Condexp
import Mathlib.Probability.Kernel.Composition.MapComap
import Definitions.Def_Malliavin_PredictableKernel
import Theorems.Thm_Malliavin_finiteHorizonProductMeasure_eq_restrict
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
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal InnerProductSpace
open Malliavin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
namespace Malliavin
theorem _root_.solution
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›) (U : TimeProcessL2 P) (T : ℝ≥0) :
    (predictableProjection 𝓕 U : ℝ≥0 × W → ℝ)
      =ᵐ[finiteHorizonProductMeasure P T]
        fun p => ∫ q, U q
          ∂condExpKernel (finiteHorizonProductMeasure P T) 𝓕.predictable p := by
  let μ := nonnegativeLebesgueMeasure.prod P
  let S : Set (ℝ≥0 × W) := Set.Iic T ×ˢ Set.univ
  let μT := finiteHorizonProductMeasure P T
  have hμT : μT = μ.restrict S := by
    simpa only [μT, μ, S] using finiteHorizonProductMeasure_eq_restrict (P := P) T
  have hS : MeasurableSet[𝓕.predictable] S := by
    have hpre : MeasurableSet[𝓕.predictable]
        (Prod.fst ⁻¹' Set.Iic T : Set (ℝ≥0 × W)) :=
      (measurable_fst_predictable 𝓕) measurableSet_Iic
    rw [show S = Prod.fst ⁻¹' Set.Iic T by
      ext p
      simp only [S, Set.mem_prod, Set.mem_Iic, Set.mem_univ, and_true,
        Set.mem_preimage]]
    exact hpre
  have hμT_le : μT ≤ μ := by
    rw [hμT]
    exact Measure.restrict_le_self
  have hU_mem : MemLp (U : ℝ≥0 × W → ℝ) 2 μT :=
    (Lp.memLp U).mono_measure hμT_le
  have hU_int : Integrable (U : ℝ≥0 × W → ℝ) μT :=
    hU_mem.integrable fact_one_le_two_ennreal.elim
  let Q := predictableProjection 𝓕 U
  have hQ_mem : MemLp (Q : ℝ≥0 × W → ℝ) 2 μT :=
    (Lp.memLp (Q : TimeProcessL2 P)).mono_measure hμT_le
  have hQ_int : Integrable (Q : ℝ≥0 × W → ℝ) μT :=
    hQ_mem.integrable fact_one_le_two_ennreal.elim
  have hQ_meas : AEStronglyMeasurable[𝓕.predictable]
      (Q : ℝ≥0 × W → ℝ) μT :=
    (lpMeas.aestronglyMeasurable Q).mono_measure hμT_le
  have hQ_cond : (Q : ℝ≥0 × W → ℝ) =ᵐ[μT]
      μT[(U : ℝ≥0 × W → ℝ) | 𝓕.predictable] := by
    apply ae_eq_condExp_of_forall_setIntegral_eq (predictable_le_prod 𝓕) hU_int
    · intro s _ _
      exact hQ_int.integrableOn
    · intro s hs _
      have hsS : MeasurableSet[𝓕.predictable] (s ∩ S) := hs.inter hS
      have hμsS : μ (s ∩ S) ≠ ∞ := by
        apply ne_top_of_le_ne_top
          (show μ S ≠ ∞ from ?_)
          (measure_mono Set.inter_subset_right)
        change (nonnegativeLebesgueMeasure.prod P)
          (Set.Iic T ×ˢ Set.univ) ≠ ∞
        rw [Measure.prod_prod]
        exact ENNReal.mul_ne_top (nonnegativeLebesgueMeasure_Iic_ne_top T)
          (measure_ne_top P Set.univ)
      change ∫ x, (Q : ℝ≥0 × W → ℝ) x ∂μT.restrict s =
        ∫ x, (U : ℝ≥0 × W → ℝ) x ∂μT.restrict s
      rw [hμT, Measure.restrict_restrict ((predictable_le_prod 𝓕) s hs)]
      simpa only [Q, predictableProjection] using
        integral_condExpL2_eq (predictable_le_prod 𝓕) U hsS hμsS
    · exact hQ_meas
  exact hQ_cond.trans
    (condExp_ae_eq_integral_condExpKernel (predictable_le_prod 𝓕) hU_int)
end Malliavin
