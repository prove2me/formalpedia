-- Prove2me | solution 1 for Malliavin.BrownianIteratedConstruction.timeDerivative_mderivClosure_brownianWickPowerLp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:34:41.714419+00:00
-- url     : https://prove2.me/submissions/c9f5ad34-7558-45d8-acf2-4c59fd7ab4bf

import Definitions.Def_Malliavin_BrownianWickPurePowerComparison
import Definitions.Def_Malliavin_BrownianMultipleIntegralBoxSpan
import Definitions.Def_Malliavin_PastCylinderDensity
import Definitions.Def_Malliavin_BrownianPurePowerDuality
import Theorems.Thm_Malliavin_BrownianIteratedConstruction_brownianStepDual_apply
import Theorems.Thm_Malliavin_BrownianIteratedConstruction_wienerIntegralEquiv_symm_ofDual_brownianStepDual
import Theorems.Thm_Malliavin_BrownianIteratedConstruction_brownianPositiveTowerLI_single
import Theorems.Thm_Malliavin_BrownianIteratedConstruction_brownianSimplexIntegralLI_apply
import Theorems.Thm_Malliavin_BrownianIteratedConstruction_coeFn_brownianWickPowerLp
import Theorems.Thm_Malliavin_BrownianIteratedConstruction_derivative_varianceHermite
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
import Theorems.Thm_Malliavin_coeFn_smulLp
import Theorems.Thm_Malliavin_cylinder_expGrowth_mem_domD12
import Theorems.Thm_Malliavin_elementaryBrownianCoefficientCLM_apply
import Theorems.Thm_Malliavin_elementaryBrownianValueLinear_apply
import Theorems.Thm_Malliavin_elementaryPredictableCoefficientCLM_apply
import Theorems.Thm_Malliavin_expectationL2_wienerIntegral
import Theorems.Thm_Malliavin_mderiv_comp
import Theorems.Thm_Malliavin_mderiv_dual
import Theorems.Thm_Malliavin_mem_symmetricSubmodule
import Theorems.Thm_Malliavin_timeDerivative_smulLp
import Theorems.Thm_P2M_Malliavin_abs_polynomial_deriv_le__df93b7f4181a
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
    (generated : IsWienerGenerated B) (v : ℝ≥0 →₀ ℝ) (n : ℕ) :
    timeDerivative hB coordinate coordinate_apply generated
        (mderivClosure P (brownianWickPowerLp hB v n)) =
      tensor (stepToLp v) ((n : ℝ) • brownianWickPowerLp hB v (n - 1)) := by
  let p := varianceHermite (‖stepToLp v‖ ^ 2) n
  let F : (Fin 1 → ℝ) → ℝ := fun y ↦ p.eval (y 0)
  let L : Fin 1 → StrongDual ℝ W := fun _ ↦ brownianStepDual coordinate v
  let C := coeffMass p + coeffMass p.derivative
  let c : ℝ := p.natDegree
  have hC : 0 ≤ C := add_nonneg (coeffMass_nonneg _) (coeffMass_nonneg _)
  have hc : 0 ≤ c := Nat.cast_nonneg _
  have hF : ContDiff ℝ 1 F := contDiff_oneCoord (contDiff_polynomial_eval p)
  have hbound : ∀ y, |F y| ≤ C * Real.exp (c * ‖y‖) := by
    intro y
    exact abs_oneCoord_le hC hc (abs_polynomial_eval_le' p) y
  have hbound' : ∀ y, ‖fderiv ℝ F y‖ ≤ C * Real.exp (c * ‖y‖) := by
    intro y
    exact norm_fderiv_oneCoord_le (contDiff_polynomial_eval p) hC hc
      (abs_polynomial_deriv_le' p) y
  have heq :
      (memLp_cylinder_expGrowth P hF hC hc hbound L).toLp _ =
        brownianWickPowerLp hB v n := by
    apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp
        (memLp_cylinder_expGrowth P hF hC hc hbound L),
      coeFn_brownianWickPowerLp hB v n] with w hleft hright
    rw [hleft, hright]
    exact congrArg p.eval (brownianStepDual_apply coordinate coordinate_apply v w)
  have hderiv :
      (memLp_mderiv_cylinder_expGrowth P hF hC hc hbound' L).toLp _ =
        smulLp (CameronMartin.ofDual P (brownianStepDual coordinate v))
          ((n : ℝ) • brownianWickPowerLp hB v (n - 1)) := by
    apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp
        (memLp_mderiv_cylinder_expGrowth P hF hC hc hbound' L),
      coeFn_smulLp (CameronMartin.ofDual P (brownianStepDual coordinate v))
        ((n : ℝ) • brownianWickPowerLp hB v (n - 1)),
      Lp.coeFn_smul (n : ℝ) (brownianWickPowerLp hB v (n - 1)),
      coeFn_brownianWickPowerLp hB v (n - 1)] with w hleft hsmul hnsmul hwick
    rw [hleft, hsmul, hnsmul, Pi.smul_apply, hwick]
    change mderiv P (fun y ↦ p.eval (brownianStepDual coordinate v y)) w = _
    rw [mderiv_comp P ((contDiff_polynomial_eval p).differentiable one_ne_zero _)
      (brownianStepDual coordinate v).differentiableAt,
      mderiv_dual, Polynomial.deriv]
    change p.derivative.eval (brownianStepDual coordinate v w) • _ = _
    rw [show p.derivative = Polynomial.C (n : ℝ) *
        varianceHermite (‖stepToLp v‖ ^ 2) (n - 1) by
      exact derivative_varianceHermite (‖stepToLp v‖ ^ 2) n]
    simp only [Polynomial.eval_mul, Polynomial.eval_C, smul_eq_mul]
    rw [brownianStepDual_apply coordinate coordinate_apply]
  rw [← heq,
    (cylinder_expGrowth_mem_domD12 P hF hC hc hbound hbound' L).2,
    hderiv, timeDerivative_smulLp,
    wienerIntegralEquiv_symm_ofDual_brownianStepDual hB coordinate coordinate_apply generated]
end Malliavin.BrownianIteratedConstruction
