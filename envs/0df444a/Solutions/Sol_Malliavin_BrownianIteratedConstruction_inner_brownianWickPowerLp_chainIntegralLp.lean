-- Prove2me | solution 1 for Malliavin.BrownianIteratedConstruction.inner_brownianWickPowerLp_chainIntegralLp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:37:01.219265+00:00
-- url     : https://prove2.me/submissions/b715ff69-7fbd-4cdd-8c03-e4605837478b

import Definitions.Def_Malliavin_BrownianWickPurePowerComparison
import Definitions.Def_Malliavin_BrownianMultipleIntegralBoxSpan
import Definitions.Def_Malliavin_PastCylinderDensity
import Definitions.Def_Malliavin_BrownianPurePowerDuality
import Theorems.Thm_Malliavin_BrownianIteratedConstruction_brownianWickPowerLp_mem_domD12
import Theorems.Thm_Malliavin_BrownianIteratedConstruction_timeDerivative_mderivClosure_brownianWickPowerLp
import Theorems.Thm_Malliavin_BrownianIteratedConstruction_brownianPositiveTowerLI_single
import Theorems.Thm_Malliavin_BrownianIteratedConstruction_brownianSimplexIntegralLI_apply
import Theorems.Thm_Malliavin_BrownianIteratedConstruction_brownianWickPowerLp_zero
import Theorems.Thm_Malliavin_BrownianIteratedConstruction_inner_brownianWickPowerLp
import Theorems.Thm_Malliavin_BrownianIteratedConstruction_integral_brownianWickPowerLp
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
import Theorems.Thm_Malliavin_elementaryPredictable_coeLp
import Theorems.Thm_Malliavin_expectationL2_wienerIntegral
import Theorems.Thm_Malliavin_inner_predictableProjection_sub
import Theorems.Thm_Malliavin_mem_symmetricSubmodule
import Theorems.Thm_Malliavin_naturalItoDuality_natural
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
    (v : ℝ≥0 →₀ ℝ) {n : ℕ} (a : OrderedBoxIndex n) :
    inner ℝ (brownianWickPowerLp hB v n) (chainIntegralLp hB a.u a.v) =
      (n.factorial : ℝ) *
        ∏ i, inner ℝ (stepToLp v) (iocIndicator (a.u i) (a.v i)) := by
  induction n with
  | zero =>
      rw [chainIntegralLp_zero hB, ← brownianWickPowerLp_zero hB v,
        inner_brownianWickPowerLp]
      simp
  | succ n ih =>
      let headBox : OrderedBoxIndex n :=
        { u := fun i ↦ a.u i.castSucc
          v := fun i ↦ a.v i.castSucc
          valid := fun i ↦ a.valid i.castSucc
          ordered := fun i j hij ↦ a.ordered i.castSucc j.castSucc
            (Fin.castSucc_lt_castSucc_iff.mpr hij) }
      let Z := orderedChainPrefixAdapted hB hsm a.u a.v a.valid a.ordered
      let U := elementaryPredictable (Filtration.natural B hsm)
        (a.u (Fin.last n)) (a.v (Fin.last n)) Z
      let F : Malliavin.D12 P :=
        ⟨brownianWickPowerLp hB v (n + 1),
          brownianWickPowerLp_mem_domD12 hB coordinate coordinate_apply v (n + 1)⟩
      have hexpect : expectationL2 (brownianWickPowerLp hB v (n + 1)) = 0 := by
        rw [expectationL2, integral_brownianWickPowerLp hB v (Nat.succ_pos n)]
        simp
      have hdual := Malliavin.naturalItoDuality_natural hB coordinate coordinate_apply
        generated hsm rfl F U
      have hchain : chainIntegralLp hB a.u a.v = naturalItoIntegral hB hsm rfl U := by
        exact chainIntegralLp_succ_eq_naturalItoIntegral
          hB hsm a.u a.v a.valid a.ordered
      have hleft :
          inner ℝ (brownianWickPowerLp hB v (n + 1))
              (chainIntegralLp hB a.u a.v) =
            inner ℝ (predictableProjection (Filtration.natural B hsm)
              (timeDerivative hB coordinate coordinate_apply generated
                (mderivD12 P F))) U := by
        rw [hchain]
        simpa only [F, hexpect, sub_zero] using hdual
      let D := timeDerivative hB coordinate coordinate_apply generated (mderivD12 P F)
      have horth := Malliavin.inner_predictableProjection_sub
        (Filtration.natural B hsm) D U
      have hproj :
          inner ℝ (predictableProjection (Filtration.natural B hsm) D) U =
            inner ℝ D (U : TimeProcessL2 P) := by
        rw [inner_sub_left] at horth
        exact sub_eq_zero.mp horth
      rw [hleft, hproj]
      change inner ℝ
        (timeDerivative hB coordinate coordinate_apply generated
          (mderivClosure P (brownianWickPowerLp hB v (n + 1))))
        (U : TimeProcessL2 P) = _
      rw [timeDerivative_mderivClosure_brownianWickPowerLp,
        show n + 1 - 1 = n by omega, elementaryPredictable_coeLp, inner_tensor,
        real_inner_smul_left,
        show (Z : RandomL2 P) = chainIntegralLp hB headBox.u headBox.v by rfl,
        ih headBox]
      simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
        Fin.prod_univ_castSucc]
      ring
end Malliavin.BrownianIteratedConstruction
