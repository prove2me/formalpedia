-- Prove2me | solution 1 for Malliavin.BrownianIteratedConstruction.brownianSymmetricMultipleIntegralRange_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:25:06.888798+00:00
-- url     : https://prove2.me/submissions/01c439a3-893e-4288-888a-60ed2a912fe4

import Definitions.Def_Malliavin_BrownianChaosHilbertSum
import Definitions.Def_Malliavin_BrownianMultipleIntegral
import Theorems.Thm_Malliavin_BrownianIteratedConstruction_brownianMultipleIntegralCLM_apply
import Theorems.Thm_Malliavin_BrownianIteratedConstruction_exists_brownianMultipleIntegralCLM_eq_simplexIntegral
import Theorems.Thm_Malliavin_BrownianIteratedConstruction_brownianPositiveTowerLI_single
import Theorems.Thm_Malliavin_BrownianIteratedConstruction_brownianSimplexIntegralLI_apply
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
open MeasureTheory ProbabilityTheory Filter Topology
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
theorem _root_.solution
    (hB : IsPreBrownianReal B P) (n : ℕ) :
    brownianSymmetricMultipleIntegralRange hB n =
      brownianMultipleIntegralRange hB n := by
  apply le_antisymm
  · rintro _ ⟨f, rfl⟩
    refine ⟨(n.factorial : ℝ) •
      symmetrizeL ℝ (μ := nonnegativeLebesgueMeasure) n 2 f, ?_⟩
    change integralCLM hB n
      ((n.factorial : ℝ) • symmetrizeL ℝ (μ := nonnegativeLebesgueMeasure) n 2 f) =
        (n.factorial : ℝ) • integralCLM hB n
          (symmetrizeL ℝ (μ := nonnegativeLebesgueMeasure) n 2 f)
    rw [map_smul]
  · cases n with
    | zero =>
        rintro _ ⟨f, rfl⟩
        refine ⟨f, ?_⟩
        change brownianMultipleIntegralCLM hB 0 f = integralCLM hB 0 f
        rw [brownianMultipleIntegralCLM_apply]
        have hfixed :
            symmetrizeL ℝ (μ := nonnegativeLebesgueMeasure) 0 2 f = f := by
          rw [symmetrizeL_eq_self_iff]
          intro σ
          have hσ : σ = 1 := Subsingleton.elim _ _
          subst σ
          exact Filter.Eventually.of_forall fun _ => rfl
        simp only [Nat.factorial_zero, Nat.cast_one, one_smul, hfixed]
    | succ n =>
        rintro _ ⟨f, rfl⟩
        obtain ⟨g, hg⟩ := exists_brownianMultipleIntegralCLM_eq_simplexIntegral hB n
          (restrictToSimplex (n + 1) f)
        refine ⟨g, ?_⟩
        exact hg.trans rfl
end Malliavin.BrownianIteratedConstruction
