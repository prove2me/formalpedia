-- Prove2me | solution 1 for Malliavin.BrownianIteratedConstruction.brownianHomogeneousChaos_le_orderedChainSpan_closure
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:01:12.549858+00:00
-- url     : https://prove2.me/submissions/b736704c-d812-43da-a2d7-b9c43d045d30

import Definitions.Def_Malliavin_BrownianChaosMartingaleRepresentation
import Definitions.Def_Malliavin_BrownianChaosTotality
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
private theorem integralCLM_mem_brownianOrderedChainSpan_closure
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (n : ℕ) (f : IteratedKernel n) :
    integralCLM hB n f ∈ (brownianOrderedChainSpan hB).topologicalClosure := by
  cases n with
  | zero =>
      let _ : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
      let a : OrderedBoxIndex 0 :=
        { u := fun i => Fin.elim0 i
          v := fun i => Fin.elim0 i
          valid := fun i => Fin.elim0 i
          ordered := fun i => Fin.elim0 i }
      let c : ℝ := ∫ t, f t ∂iteratedKernelMeasure 0
      have hvalue : integralCLM hB 0 f = c • chainIntegralLp hB a.u a.v := by
        have hconst : integralCLM hB 0 f = Lp.const 2 P c := by
          apply Lp.ext
          exact (integralCLM_zeroOrder hB f).trans (Lp.coeFn_const 2 P c).symm
        rw [hconst, chainIntegralLp_zero]
        change (Lp.constL 2 P ℝ) c = c • (Lp.constL 2 P ℝ) 1
        simpa using map_smul (Lp.constL 2 P ℝ) c (1 : ℝ)
      rw [hvalue]
      apply Submodule.le_topologicalClosure
      exact (brownianOrderedChainSpan hB).smul_mem c <|
        Submodule.subset_span ⟨⟨0, a⟩, rfl⟩
  | succ n =>
      change positiveIntegralCLM hB n f ∈
        (brownianOrderedChainSpan hB).topologicalClosure
      change simplexIntegral hB (n + 1) (restrictToSimplex (n + 1) f) ∈
        (brownianOrderedChainSpan hB).topologicalClosure
      refine (orderedBoxDense_succ n).induction_on (restrictToSimplex (n + 1) f)
        ((brownianOrderedChainSpan hB).isClosed_topologicalClosure.preimage
          (simplexIntegral hB (n + 1)).continuous) ?_
      intro d
      rw [simplexIntegral_orderedBoxToSimplexKernel hB hsm (orderedBoxDense_succ n)]
      unfold orderedBoxToRandom
      rw [Finsupp.linearCombination_apply]
      apply Submodule.sum_mem
      intro a _ha
      apply Submodule.smul_mem
      apply Submodule.le_topologicalClosure
      exact Submodule.subset_span ⟨⟨n + 1, a⟩, rfl⟩
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
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t)) (n : ℕ) :
    (brownianHomogeneousChaos hB n : Submodule ℝ (RandomL2 P)) ≤
      (brownianOrderedChainSpan hB).topologicalClosure := by
  unfold brownianHomogeneousChaos
  apply Submodule.topologicalClosure_minimal
  · rintro _ ⟨f, rfl⟩
    exact integralCLM_mem_brownianOrderedChainSpan_closure hB hsm n f
  · exact (brownianOrderedChainSpan hB).isClosed_topologicalClosure
end Malliavin.BrownianIteratedConstruction
