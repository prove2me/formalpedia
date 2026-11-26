-- Prove2me | solution 1 for Malliavin.BrownianIteratedConstruction.norm_sq_brownianWickPowerLp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:31:32.932361+00:00
-- url     : https://prove2.me/submissions/6c21b3b0-b19e-46cd-b7b4-b80247cc06e2

import Definitions.Def_Malliavin_GaussianHermite
import Definitions.Def_Malliavin_BrownianPolynomialHermite
import Definitions.Def_Malliavin_BrownianWickIsometry
import Theorems.Thm_Malliavin_BrownianIteratedConstruction_inner_brownianWickPowerLp

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
omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [BorelSpace W]
    [SecondCountableTopology W] [IsGaussian P]
namespace Malliavin.BrownianIteratedConstruction
theorem _root_.solution (hB : IsPreBrownianReal B P)
    (v : ℝ≥0 →₀ ℝ) (n : ℕ) :
    ‖brownianWickPowerLp hB v n‖ ^ 2 =
      (n.factorial : ℝ) * (‖stepToLp v‖ ^ 2) ^ n := by
  rw [← real_inner_self_eq_norm_sq, inner_brownianWickPowerLp, if_pos rfl]
end Malliavin.BrownianIteratedConstruction
