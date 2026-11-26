-- Prove2me | solution 1 for Malliavin.BrownianIteratedConstruction.inner_brownianWickPowerLp_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:38:45.598831+00:00
-- url     : https://prove2.me/submissions/0be52341-502f-4c53-8391-287e0c21434b

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
    (v : ℝ≥0 →₀ ℝ) {m n : ℕ} (hmn : m ≠ n) :
    inner ℝ (brownianWickPowerLp hB v m) (brownianWickPowerLp hB v n) = 0 := by
  rw [inner_brownianWickPowerLp, if_neg hmn]
end Malliavin.BrownianIteratedConstruction
