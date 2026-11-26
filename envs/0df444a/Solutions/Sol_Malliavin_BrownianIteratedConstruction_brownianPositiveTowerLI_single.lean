-- Prove2me | solution 1 for Malliavin.BrownianIteratedConstruction.brownianPositiveTowerLI_single
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:01:46.821809+00:00
-- url     : https://prove2.me/submissions/3f59a524-6f86-4a61-8abb-3c388daadab0

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
    brownianPositiveTowerLI hB hsm (lp.single 2 n f) =
      simplexIntegral hB (n + 1) f := by
  exact (brownianSimplexIntegralLI_orthogonalFamily hB hsm
    ).linearIsometry_apply_single f
end Malliavin.BrownianIteratedConstruction
