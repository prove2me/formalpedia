-- Prove2me | solution 1 for Malliavin.BrownianIteratedConstruction.inner_brownianWickPowerLp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:29:53.043951+00:00
-- url     : https://prove2.me/submissions/7f62e6c6-825b-478f-ba4e-881eeb99d9ed

import Definitions.Def_Malliavin_GaussianHermite
import Definitions.Def_Malliavin_BrownianPolynomialHermite
import Definitions.Def_Malliavin_BrownianWickIsometry
import Theorems.Thm_Malliavin_BrownianIteratedConstruction_map_stepSum_eq_gaussianReal
import Theorems.Thm_Malliavin_BrownianIteratedConstruction_brownianPositiveTowerLI_single
import Theorems.Thm_Malliavin_BrownianIteratedConstruction_brownianSimplexIntegralLI_apply
import Theorems.Thm_Malliavin_BrownianIteratedConstruction_coeFn_brownianWickPowerLp
import Theorems.Thm_Malliavin_BrownianIteratedConstruction_integral_varianceHermite_mul_centeredGaussian
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
import Theorems.Thm_Malliavin_hasGaussianLaw_stepSum
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
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace
noncomputable section
open Malliavin Malliavin.BrownianIteratedConstruction
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
  {B : ℝ≥0 → W → ℝ}
omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [BorelSpace W]
    [SecondCountableTopology W] [IsGaussian P]
namespace Malliavin.BrownianIteratedConstruction
theorem _root_.solution (hB : IsPreBrownianReal B P)
    (v : ℝ≥0 →₀ ℝ) (m n : ℕ) :
    inner ℝ (brownianWickPowerLp hB v m) (brownianWickPowerLp hB v n) =
      if m = n then m.factorial * (‖stepToLp v‖ ^ 2) ^ m else 0 := by
  rw [MeasureTheory.L2.inner_def]
  calc
    (∫ w, inner ℝ (brownianWickPowerLp hB v m w)
        (brownianWickPowerLp hB v n w) ∂P) =
        ∫ w, (varianceHermite (‖stepToLp v‖ ^ 2) m).eval (stepSum B v w) *
          (varianceHermite (‖stepToLp v‖ ^ 2) n).eval (stepSum B v w) ∂P := by
      apply integral_congr_ae
      filter_upwards [coeFn_brownianWickPowerLp hB v m,
        coeFn_brownianWickPowerLp hB v n] with w hm hn
      rw [hm, hn]
      simp only [RCLike.inner_apply, conj_trivial]
      ring
    _ = ∫ x, (varianceHermite (‖stepToLp v‖ ^ 2) m).eval x *
          (varianceHermite (‖stepToLp v‖ ^ 2) n).eval x ∂P.map (stepSum B v) := by
      symm
      rw [integral_map (hasGaussianLaw_stepSum hB v).aemeasurable (by fun_prop)]
    _ = ∫ x, (varianceHermite (‖stepToLp v‖ ^ 2) m).eval x *
          (varianceHermite (‖stepToLp v‖ ^ 2) n).eval x
          ∂gaussianReal 0 (‖stepToLp v‖₊ ^ 2) := by
      rw [map_stepSum_eq_gaussianReal hB v]
    _ = if m = n then m.factorial * (‖stepToLp v‖ ^ 2) ^ m else 0 := by
      have hvariance : ((↑(‖stepToLp v‖₊ ^ 2) : ℝ)) = ‖stepToLp v‖ ^ 2 := by
        simp
      have horth :=
        integral_varianceHermite_mul_centeredGaussian (‖stepToLp v‖₊ ^ 2) m n
      rw [hvariance] at horth
      exact horth
end Malliavin.BrownianIteratedConstruction
