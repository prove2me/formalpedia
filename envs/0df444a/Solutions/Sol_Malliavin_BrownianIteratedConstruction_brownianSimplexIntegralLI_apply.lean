-- Prove2me | solution 1 for Malliavin.BrownianIteratedConstruction.brownianSimplexIntegralLI_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:01:55.970953+00:00
-- url     : https://prove2.me/submissions/8bf1fec6-3e40-4d3b-8f00-a9079a6cb3ba

import Definitions.Def_Malliavin_BrownianChaosTotality
import Definitions.Def_Malliavin_BrownianChaosHilbertSum

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
    (n : ℕ) (f : IteratedIntegralConstruction.SimplexKernel (n + 1)) :
    brownianSimplexIntegralLI hB hsm n f = simplexIntegral hB (n + 1) f :=
  rfl
end Malliavin.BrownianIteratedConstruction
