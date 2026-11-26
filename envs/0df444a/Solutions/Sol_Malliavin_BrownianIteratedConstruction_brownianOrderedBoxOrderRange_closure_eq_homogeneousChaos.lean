-- Prove2me | solution 1 for Malliavin.BrownianIteratedConstruction.brownianOrderedBoxOrderRange_closure_eq_homogeneousChaos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:20:17.533073+00:00
-- url     : https://prove2.me/submissions/48947273-23b8-4bae-91dd-7dc50dbd6173

import Definitions.Def_Malliavin_BrownianMultipleIntegralBox
import Definitions.Def_Malliavin_BrownianMultipleIntegralBoxSpan
import Theorems.Thm_Malliavin_BrownianIteratedConstruction_brownianHomogeneousChaos_succ_eq_range_simplexIntegralLI


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
omit [CompleteSpace W] [BorelSpace W]
namespace Malliavin.BrownianIteratedConstruction
theorem _root_.solution
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t)) (n : ℕ) :
    (brownianOrderedBoxOrderRange hB (n + 1)).topologicalClosure =
      (brownianHomogeneousChaos hB (n + 1) : Submodule ℝ (RandomL2 P)) := by
  apply le_antisymm
  · apply Submodule.topologicalClosure_minimal
    · rintro _ ⟨c, rfl⟩
      rw [← simplexIntegral_orderedBoxToSimplexKernel hB hsm
        (orderedBoxDense_succ n)]
      rw [brownianHomogeneousChaos_succ_eq_range_simplexIntegralLI hB hsm]
      exact ⟨orderedBoxToSimplexKernel (n + 1) c, rfl⟩
    · exact (brownianHomogeneousChaos hB (n + 1)).isClosed
  · rw [brownianHomogeneousChaos_succ_eq_range_simplexIntegralLI hB hsm]
    rintro _ ⟨f, rfl⟩
    change simplexIntegral hB (n + 1) f ∈
      (brownianOrderedBoxOrderRange hB (n + 1)).topologicalClosure
    refine (orderedBoxDense_succ n).induction_on f
      ((brownianOrderedBoxOrderRange hB (n + 1)).isClosed_topologicalClosure.preimage
        (simplexIntegral hB (n + 1)).continuous) ?_
    intro c
    rw [simplexIntegral_orderedBoxToSimplexKernel hB hsm (orderedBoxDense_succ n)]
    apply Submodule.le_topologicalClosure
    exact ⟨c, rfl⟩
end Malliavin.BrownianIteratedConstruction
