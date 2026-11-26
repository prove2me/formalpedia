-- Prove2me | solution 1 for Malliavin.BrownianIteratedConstruction.positiveIntegralCLM_box
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:54:38.654485+00:00
-- url     : https://prove2.me/submissions/a9f4d37a-4146-4241-9132-35efa5c52887

import Definitions.Def_Malliavin_ItoConstruction
import Definitions.Def_Malliavin_BrownianIterated
import Theorems.Thm_Malliavin_BrownianIteratedConstruction_simplexIntegral_orderedBoxSimplexKernel
import Theorems.Thm_Malliavin_BrownianIteratedConstruction_restrictToSimplex_boxKernel

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal InnerProductSpace
noncomputable section
open Malliavin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
  {B : ℝ≥0 → W → ℝ}
open Malliavin.BrownianIteratedConstruction
omit [CompleteSpace W] [BorelSpace W]
namespace Malliavin.BrownianIteratedConstruction
theorem _root_.solution
    (hB : IsPreBrownianReal B P) (hsm : ∀ s, StronglyMeasurable (B s))
    {n : ℕ} (hdense : OrderedBoxDense (n + 1)) (a : OrderedBoxIndex (n + 1)) :
    positiveIntegralCLM hB n (boxKernel a.u a.v) = chainIntegralLp hB a.u a.v := by
  rw [positiveIntegralCLM, ContinuousLinearMap.comp_apply, restrictToSimplex_boxKernel,
    simplexIntegral_orderedBoxSimplexKernel hB hsm hdense]
end Malliavin.BrownianIteratedConstruction
