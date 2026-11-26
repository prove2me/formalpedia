-- Prove2me | solution 1 for Malliavin.BrownianIteratedConstruction.brownianHomogeneousChaos_succ_eq_range_simplexIntegralLI
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:02:30.507508+00:00
-- url     : https://prove2.me/submissions/9fc9534a-258a-42cb-9ab9-2033c6a2e44b

import Definitions.Def_Malliavin_BrownianChaosTotality
import Definitions.Def_Malliavin_BrownianChaosHilbertSum
import Theorems.Thm_Malliavin_BrownianIteratedConstruction_integralCLM_mem_brownianHomogeneousChaos
import Theorems.Thm_Malliavin_BrownianIteratedConstruction_positiveIntegralCLM_box


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
    (brownianHomogeneousChaos hB (n + 1) : Submodule ℝ (RandomL2 P)) =
      LinearMap.range (brownianSimplexIntegralLI hB hsm n).toLinearMap := by
  apply le_antisymm
  · unfold brownianHomogeneousChaos brownianMultipleIntegralRange
    apply Submodule.topologicalClosure_minimal
    · rintro _ ⟨f, rfl⟩
      exact ⟨restrictToSimplex (n + 1) f, rfl⟩
    · exact (brownianSimplexIntegralLI hB hsm n).isometry.isClosedEmbedding.isClosed_range
  · rintro _ ⟨f, rfl⟩
    change simplexIntegral hB (n + 1) f ∈ brownianHomogeneousChaos hB (n + 1)
    refine (orderedBoxDense_succ n).induction_on f
      ((brownianHomogeneousChaos hB (n + 1)).isClosed.preimage
        (simplexIntegral hB (n + 1)).continuous) ?_
    intro c
    rw [simplexIntegral_orderedBoxToSimplexKernel hB hsm (orderedBoxDense_succ n)]
    unfold orderedBoxToRandom
    rw [Finsupp.linearCombination_apply]
    apply Submodule.sum_mem
    intro a _ha
    apply Submodule.smul_mem
    rw [← positiveIntegralCLM_box hB hsm (orderedBoxDense_succ n) a]
    exact integralCLM_mem_brownianHomogeneousChaos hB (n + 1)
      (boxKernel a.u a.v)
end Malliavin.BrownianIteratedConstruction
