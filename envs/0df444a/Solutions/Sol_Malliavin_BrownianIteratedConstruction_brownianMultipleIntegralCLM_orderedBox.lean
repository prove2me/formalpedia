-- Prove2me | solution 1 for Malliavin.BrownianIteratedConstruction.brownianMultipleIntegralCLM_orderedBox
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:22:06.730511+00:00
-- url     : https://prove2.me/submissions/b5b57bf1-ec13-4cc4-90b1-2ef119bdf909

import Definitions.Def_Malliavin_BrownianMultipleIntegral
import Definitions.Def_Malliavin_BrownianMultipleIntegralBox
import Theorems.Thm_Malliavin_BrownianIteratedConstruction_restrictToSimplex_symmetrizeL_boxKernel
import Theorems.Thm_Malliavin_BrownianIteratedConstruction_brownianMultipleIntegralCLM_apply
import Theorems.Thm_Malliavin_BrownianIteratedConstruction_brownianPositiveTowerLI_single
import Theorems.Thm_Malliavin_BrownianIteratedConstruction_brownianSimplexIntegralLI_apply
import Theorems.Thm_Malliavin_BrownianIteratedConstruction_simplexIntegral_orderedBoxSimplexKernel
import Theorems.Thm_Malliavin_CameronMartin_covarianceMap_apply
import Theorems.Thm_Malliavin_CameronMartin_densityExponent_zero
import Theorems.Thm_Malliavin_CameronMartin_density_toReal
import Theorems.Thm_Malliavin_CameronMartin_density_zero
import Theorems.Thm_Malliavin_CameronMartin_expectationMap_apply
import Theorems.Thm_Malliavin_CameronMartin_inclusion_apply
import Theorems.Thm_Malliavin_CameronMartin_realDensity_zero
import Theorems.Thm_Malliavin_CameronMartin_translated_zero
import Theorems.Thm_Malliavin_IteratedIntegralFamily_box_zero
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
import Theorems.Thm_Malliavin_symmetrizeL_eq_self_iff
attribute [local simp] Malliavin.BrownianIteratedConstruction.brownianPositiveTowerLI_single
attribute [local simp] Malliavin.BrownianIteratedConstruction.brownianSimplexIntegralLI_apply
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
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal InnerProductSpace
noncomputable section
open Malliavin Malliavin.BrownianIteratedConstruction
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
  {B : ℝ≥0 → W → ℝ}
omit [CompleteSpace W] [BorelSpace W]
namespace Malliavin.BrownianIteratedConstruction
theorem _root_.solution
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {n : ℕ} (a : OrderedBoxIndex n) :
    brownianMultipleIntegralCLM hB n (boxKernel a.u a.v) =
      chainIntegralLp hB a.u a.v := by
  cases n with
  | zero =>
      rw [brownianMultipleIntegralCLM_apply]
      have hfixed :
          symmetrizeL ℝ (μ := nonnegativeLebesgueMeasure) 0 2
              (boxKernel a.u a.v) =
            boxKernel a.u a.v := by
        rw [symmetrizeL_eq_self_iff]
        intro σ
        have hσ : σ = 1 := Subsingleton.elim _ _
        subst σ
        exact Eventually.of_forall fun _ ↦ rfl
      simp only [Nat.factorial_zero, Nat.cast_one, one_smul, hfixed]
      apply Lp.ext
      exact (IteratedIntegralFamily.box_zero (B := B)
        (family hB hsm positiveOrderedBoxDense) a.u a.v).trans
          (coeFn_chainIntegralLp hB a.u a.v).symm
  | succ n =>
      rw [brownianMultipleIntegralCLM_apply]
      change ((n + 1).factorial : ℝ) •
          simplexIntegral hB (n + 1)
            (restrictToSimplex (n + 1)
              (symmetrizeL ℝ (μ := nonnegativeLebesgueMeasure) (n + 1) 2
                (boxKernel a.u a.v))) =
        chainIntegralLp hB a.u a.v
      rw [restrictToSimplex_symmetrizeL_boxKernel a, map_smul, smul_smul]
      have hfac : ((n + 1).factorial : ℝ) ≠ 0 := by
        exact_mod_cast (n + 1).factorial_ne_zero
      rw [mul_inv_cancel₀ hfac, one_smul]
      exact simplexIntegral_orderedBoxSimplexKernel hB hsm
        (positiveOrderedBoxDense n) a
end Malliavin.BrownianIteratedConstruction
