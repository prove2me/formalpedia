-- Prove2me | solution 1 for Malliavin.BrownianIteratedConstruction.denseRange_restrictToSimplex_symmetrizeL_orderedBoxToIteratedKernel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:40:08.915916+00:00
-- url     : https://prove2.me/submissions/15762940-d0e4-450c-98ce-3ea4c38ef3f0

import Definitions.Def_Malliavin_BrownianMultipleIntegralBox
import Definitions.Def_Malliavin_BrownianMultipleIntegralBoxSpan
import Theorems.Thm_Malliavin_BrownianIteratedConstruction_restrictToSimplex_symmetrizeL_orderedBoxToIteratedKernel

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
omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [MeasurableSpace W]
    [BorelSpace W] [SecondCountableTopology W] [IsGaussian P]
namespace Malliavin.BrownianIteratedConstruction
theorem _root_.solution
    (n : ℕ) (hdense : OrderedBoxDense n) :
    DenseRange fun c : OrderedBoxIndex n →₀ ℝ ↦
      restrictToSimplex n
        (symmetrizeL ℝ (μ := nonnegativeLebesgueMeasure) n 2
          (orderedBoxToIteratedKernel n c)) := by
  have hfac : ((n.factorial : ℝ)) ≠ 0 := by
    exact_mod_cast n.factorial_ne_zero
  have hscale : Function.Surjective
      (fun f : IteratedIntegralConstruction.SimplexKernel n ↦
        ((n.factorial : ℝ)⁻¹) • f) := by
    intro f
    refine ⟨(n.factorial : ℝ) • f, ?_⟩
    change ((n.factorial : ℝ)⁻¹) • ((n.factorial : ℝ) • f) = f
    rw [smul_smul, inv_mul_cancel₀ hfac, one_smul]
  have hcomp := hscale.denseRange.comp hdense (continuous_const_smul _)
  have heq :
      (fun c : OrderedBoxIndex n →₀ ℝ ↦
        restrictToSimplex n
          (symmetrizeL ℝ (μ := nonnegativeLebesgueMeasure) n 2
            (orderedBoxToIteratedKernel n c))) =
        (fun f : IteratedIntegralConstruction.SimplexKernel n ↦
          ((n.factorial : ℝ)⁻¹) • f) ∘ orderedBoxToSimplexKernel n := by
    funext c
    exact restrictToSimplex_symmetrizeL_orderedBoxToIteratedKernel n c
  rw [heq]
  exact hcomp
end Malliavin.BrownianIteratedConstruction
