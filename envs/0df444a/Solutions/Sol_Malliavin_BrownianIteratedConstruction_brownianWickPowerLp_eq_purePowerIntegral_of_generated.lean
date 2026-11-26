-- Prove2me | solution 1 for Malliavin.BrownianIteratedConstruction.brownianWickPowerLp_eq_purePowerIntegral_of_generated
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:41:01.361809+00:00
-- url     : https://prove2.me/submissions/3fb276f5-c946-486f-81f2-5358015a9675

import Definitions.Def_Malliavin_BrownianWickPurePowerComparison
import Definitions.Def_Malliavin_BrownianMultipleIntegralBoxSpan
import Definitions.Def_Malliavin_PastCylinderDensity
import Definitions.Def_Malliavin_BrownianPurePowerDuality
import Theorems.Thm_Malliavin_BrownianIteratedConstruction_inner_brownianWickPowerLp_chainIntegralLp_eq_purePower
import Theorems.Thm_Malliavin_BrownianIteratedConstruction_brownianOrderedBoxOrderRange_closure_eq_homogeneousChaos
import Theorems.Thm_Malliavin_BrownianIteratedConstruction_brownianPositiveTowerLI_single
import Theorems.Thm_Malliavin_BrownianIteratedConstruction_brownianPurePowerIntegral_mem_brownianHomogeneousChaos
import Theorems.Thm_Malliavin_BrownianIteratedConstruction_brownianPurePowerIntegral_zero_step
import Theorems.Thm_Malliavin_BrownianIteratedConstruction_brownianSimplexIntegralLI_apply
import Theorems.Thm_Malliavin_BrownianIteratedConstruction_brownianWickPowerLp_eq_purePowerIntegral_iff_inner
import Theorems.Thm_Malliavin_BrownianIteratedConstruction_inner_brownianPurePowerIntegral
import Theorems.Thm_Malliavin_BrownianIteratedConstruction_polynomialFamilyLinearMap_X_pow
import Theorems.Thm_Malliavin_CameronMartin_covarianceMap_apply
import Theorems.Thm_Malliavin_CameronMartin_densityExponent_zero
import Theorems.Thm_Malliavin_CameronMartin_density_toReal
import Theorems.Thm_Malliavin_CameronMartin_density_zero
import Theorems.Thm_Malliavin_CameronMartin_expectationMap_apply
import Theorems.Thm_Malliavin_CameronMartin_inclusion_apply
import Theorems.Thm_Malliavin_CameronMartin_realDensity_zero
import Theorems.Thm_Malliavin_CameronMartin_translated_zero
import Theorems.Thm_Malliavin_bestNaturalItoIntegrand_centeredNaturalItoIntegral
import Theorems.Thm_Malliavin_centeredNaturalItoEquiv_apply
import Theorems.Thm_Malliavin_centeredNaturalItoIntegralIsometry_apply
import Theorems.Thm_Malliavin_centeredPartL2_coe
import Theorems.Thm_Malliavin_centeredWienerIntegral_coe
import Theorems.Thm_Malliavin_elementaryBrownianCoefficientCLM_apply
import Theorems.Thm_Malliavin_elementaryBrownianValueLinear_apply
import Theorems.Thm_Malliavin_elementaryPredictableCoefficientCLM_apply
import Theorems.Thm_Malliavin_expectationL2_wienerIntegral
import Theorems.Thm_Malliavin_mem_symmetricSubmodule
attribute [local simp] Malliavin.BrownianIteratedConstruction.brownianPositiveTowerLI_single
attribute [local simp] Malliavin.BrownianIteratedConstruction.brownianSimplexIntegralLI_apply
attribute [local simp] Malliavin.BrownianIteratedConstruction.polynomialFamilyLinearMap_X_pow
attribute [local simp] Malliavin.CameronMartin.covarianceMap_apply
attribute [local simp] Malliavin.CameronMartin.densityExponent_zero
attribute [local simp] Malliavin.CameronMartin.density_toReal
attribute [local simp] Malliavin.CameronMartin.density_zero
attribute [local simp] Malliavin.CameronMartin.expectationMap_apply
attribute [local simp] Malliavin.CameronMartin.inclusion_apply
attribute [local simp] Malliavin.CameronMartin.realDensity_zero
attribute [local simp] Malliavin.CameronMartin.translated_zero
attribute [local simp] Malliavin.bestNaturalItoIntegrand_centeredNaturalItoIntegral
attribute [local simp] Malliavin.centeredNaturalItoEquiv_apply
attribute [local simp] Malliavin.centeredNaturalItoIntegralIsometry_apply
attribute [local simp] Malliavin.centeredPartL2_coe
attribute [local simp] Malliavin.centeredWienerIntegral_coe
attribute [local simp] Malliavin.elementaryBrownianCoefficientCLM_apply
attribute [local simp] Malliavin.elementaryBrownianValueLinear_apply
attribute [local simp] Malliavin.elementaryPredictableCoefficientCLM_apply
attribute [local simp] Malliavin.expectationL2_wienerIntegral
attribute [local simp] Malliavin.mem_symmetricSubmodule



set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
noncomputable section
open Malliavin Malliavin.BrownianIteratedConstruction
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
  {B : ℝ≥0 → W → ℝ}
namespace Malliavin.BrownianIteratedConstruction
theorem _root_.solution
    (hB : IsPreBrownianReal B P) (coordinate : ℝ≥0 → StrongDual ℝ W)
    (coordinate_apply : ∀ t w, B t w = coordinate t w)
    (generated : IsWienerGenerated B) (hsm : ∀ t, StronglyMeasurable (B t))
    (v : ℝ≥0 →₀ ℝ) (n : ℕ) :
    brownianWickPowerLp hB v n =
      brownianPurePowerIntegral hB n (stepToLp v) := by
  cases n with
  | zero => exact (brownianPurePowerIntegral_zero_step hB v).symm
  | succ n =>
      apply (brownianWickPowerLp_eq_purePowerIntegral_iff_inner
        hB hsm v (n + 1)).2
      let wick := brownianWickPowerLp hB v (n + 1)
      let pure := brownianPurePowerIntegral hB (n + 1) (stepToLp v)
      let T : RandomL2 P →L[ℝ] ℝ := innerSL ℝ wick - innerSL ℝ pure
      let K : Submodule ℝ (RandomL2 P) := T.ker
      have hrange : brownianOrderedBoxOrderRange hB (n + 1) ≤ K := by
        rintro z ⟨c, rfl⟩
        change T (orderedBoxToRandom hB (n + 1) c) = 0
        change inner ℝ wick (orderedBoxToRandom hB (n + 1) c) -
          inner ℝ pure (orderedBoxToRandom hB (n + 1) c) = 0
        unfold orderedBoxToRandom
        simp only [Finsupp.linearCombination_apply, Finsupp.sum]
        rw [inner_sum, inner_sum]
        simp only [real_inner_smul_right]
        apply sub_eq_zero.mpr
        apply Finset.sum_congr rfl
        intro a ha
        rw [inner_brownianWickPowerLp_chainIntegralLp_eq_purePower
          hB coordinate coordinate_apply generated hsm]
      have hclosure :
          (brownianOrderedBoxOrderRange hB (n + 1)).topologicalClosure ≤ K := by
        apply Submodule.topologicalClosure_minimal
        · exact hrange
        · exact ContinuousLinearMap.isClosed_ker T
      have hpure : pure ∈ K := by
        apply hclosure
        rw [brownianOrderedBoxOrderRange_closure_eq_homogeneousChaos hB hsm n]
        exact brownianPurePowerIntegral_mem_brownianHomogeneousChaos
          hB (n + 1) (stepToLp v)
      change inner ℝ wick pure - inner ℝ pure pure = 0 at hpure
      rw [sub_eq_zero] at hpure
      rw [hpure, inner_brownianPurePowerIntegral hB hsm,
        real_inner_self_eq_norm_sq]
end Malliavin.BrownianIteratedConstruction
