-- Prove2me | solution 1 for Malliavin.BrownianIteratedConstruction.simplexIntegral_mem_naturalItoRange_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:49:30.909169+00:00
-- url     : https://prove2.me/submissions/b84c5842-43bb-4802-8615-d085dd9f247a

import Definitions.Def_Malliavin_BrownianOrderedBoxDensity
import Definitions.Def_Malliavin_NaturalClarkOcone
import Definitions.Def_Malliavin_NaturalItoRange
import Definitions.Def_Malliavin_BrownianChaos
import Theorems.Thm_Malliavin_isClosed_naturalItoRange

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
private theorem chainIntegralLp_mem_naturalItoRange
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {n : ℕ} (a : OrderedBoxIndex (n + 1)) :
    chainIntegralLp hB a.u a.v ∈ naturalItoRange hB hsm rfl := by
  refine ⟨elementaryPredictable (Filtration.natural B hsm)
    (a.u (Fin.last n)) (a.v (Fin.last n))
    (orderedChainPrefixAdapted hB hsm a.u a.v a.valid a.ordered), ?_⟩
  exact (chainIntegralLp_succ_eq_naturalItoIntegral
    hB hsm a.u a.v a.valid a.ordered).symm
omit [CompleteSpace W] [BorelSpace W] in
private theorem orderedBoxToRandom_mem_naturalItoRange
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {n : ℕ} (c : OrderedBoxIndex (n + 1) →₀ ℝ) :
    orderedBoxToRandom hB (n + 1) c ∈ naturalItoRange hB hsm rfl := by
  unfold orderedBoxToRandom
  rw [Finsupp.linearCombination_apply]
  apply Submodule.sum_mem
  intro a _ha
  exact Submodule.smul_mem _ _ (chainIntegralLp_mem_naturalItoRange hB hsm a)
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
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓅 = Filtration.natural B hsm) {n : ℕ}
    (f : IteratedIntegralConstruction.SimplexKernel (n + 1)) :
    simplexIntegral hB (n + 1) f ∈ naturalItoRange hB hsm hnat := by
  subst 𝓅
  refine (orderedBoxDense_succ n).induction_on f
    ((isClosed_naturalItoRange hB hsm rfl).preimage
      (simplexIntegral hB (n + 1)).continuous) ?_
  intro c
  rw [simplexIntegral_orderedBoxToSimplexKernel hB hsm (orderedBoxDense_succ n)]
  exact orderedBoxToRandom_mem_naturalItoRange hB hsm c
end Malliavin.BrownianIteratedConstruction
