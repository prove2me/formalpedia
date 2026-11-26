-- Prove2me | solution 1 for Malliavin.BrownianIteratedConstruction.integral_pow_four_centeredGaussian
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:26:44.380837+00:00
-- url     : https://prove2.me/submissions/cf260b47-985e-4f68-b839-08d2352b7570

import Definitions.Def_Malliavin_BrownianHermite
import Mathlib.Probability.Distributions.Gaussian.Real
import Definitions.Def_Malliavin_GaussianHermite
import Theorems.Thm_Malliavin_BrownianIteratedConstruction_integral_pow_succ_centeredGaussian
import Theorems.Thm_Malliavin_BrownianIteratedConstruction_integral_sq_centeredGaussian

set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped NNReal
noncomputable section
open Malliavin Malliavin.BrownianIteratedConstruction
namespace Malliavin.BrownianIteratedConstruction
theorem _root_.solution (variance : ℝ≥0) :
    (∫ x : ℝ, x ^ 4 ∂gaussianReal 0 variance) = 3 * (variance : ℝ) ^ 2 := by
  rw [show (4 : ℕ) = 3 + 1 by norm_num,
    integral_pow_succ_centeredGaussian, integral_sq_centeredGaussian]
  ring
end Malliavin.BrownianIteratedConstruction
