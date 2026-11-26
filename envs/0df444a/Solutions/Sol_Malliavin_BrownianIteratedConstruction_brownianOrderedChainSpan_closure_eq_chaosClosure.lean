-- Prove2me | solution 1 for Malliavin.BrownianIteratedConstruction.brownianOrderedChainSpan_closure_eq_chaosClosure
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:22:07.730698+00:00
-- url     : https://prove2.me/submissions/fb96fa7c-d046-4ea5-86c8-102c0096d5d2

import Definitions.Def_Malliavin_BrownianChaosMartingaleRepresentation
import Definitions.Def_Malliavin_BrownianChaosTotality
import Theorems.Thm_Malliavin_BrownianIteratedConstruction_brownianHomogeneousChaos_le_orderedChainSpan_closure
import Theorems.Thm_Malliavin_BrownianIteratedConstruction_integralCLM_mem_brownianHomogeneousChaos
import Theorems.Thm_Malliavin_BrownianIteratedConstruction_positiveIntegralCLM_box
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


section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
noncomputable section
namespace Malliavin.BrownianIteratedConstruction
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
  {B : ℝ≥0 → W → ℝ}
omit [CompleteSpace W] [BorelSpace W] in
private theorem chainIntegralLp_mem_iSup_brownianHomogeneousChaos
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {n : ℕ} (a : OrderedBoxIndex n) :
    chainIntegralLp hB a.u a.v ∈
      ⨆ k : ℕ, (brownianHomogeneousChaos hB k : Submodule ℝ (RandomL2 P)) := by
  cases n with
  | zero =>
      let _ : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
      let f : IteratedKernel 0 := Lp.const 2 (iteratedKernelMeasure 0) (1 : ℝ)
      have hfint : ∫ t, f t ∂iteratedKernelMeasure 0 = 1 := by
        rw [integral_congr_ae (Lp.coeFn_const 2 (iteratedKernelMeasure 0) (1 : ℝ))]
        simp
      have hvalue : integralCLM hB 0 f = chainIntegralLp hB a.u a.v := by
        apply Lp.ext
        filter_upwards [integralCLM_zeroOrder hB f,
          coeFn_chainIntegralLp hB a.u a.v] with w hw hchain
        rw [hw, hfint, hchain]
        simp [chainIntegral]
      apply le_iSup (fun k : ℕ =>
        (brownianHomogeneousChaos hB k : Submodule ℝ (RandomL2 P))) 0
      rw [← hvalue]
      exact integralCLM_mem_brownianHomogeneousChaos hB 0 f
  | succ n =>
      apply le_iSup (fun k : ℕ =>
        (brownianHomogeneousChaos hB k : Submodule ℝ (RandomL2 P))) (n + 1)
      rw [← positiveIntegralCLM_box hB hsm (orderedBoxDense_succ n) a]
      exact integralCLM_mem_brownianHomogeneousChaos hB (n + 1)
        (boxKernel a.u a.v)
end Malliavin.BrownianIteratedConstruction
end
end

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
omit [CompleteSpace W] [BorelSpace W]
namespace Malliavin.BrownianIteratedConstruction
theorem _root_.solution
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t)) :
    (brownianOrderedChainSpan hB).topologicalClosure =
      (⨆ n : ℕ, (brownianHomogeneousChaos hB n : Submodule ℝ (RandomL2 P))
        ).topologicalClosure := by
  apply le_antisymm
  · apply Submodule.topologicalClosure_mono
    apply Submodule.span_le.mpr
    rintro F ⟨a, rfl⟩
    exact chainIntegralLp_mem_iSup_brownianHomogeneousChaos hB hsm a.2
  · apply Submodule.topologicalClosure_minimal
    · exact iSup_le fun n =>
        brownianHomogeneousChaos_le_orderedChainSpan_closure hB hsm n
    · exact (brownianOrderedChainSpan hB).isClosed_topologicalClosure
end Malliavin.BrownianIteratedConstruction
