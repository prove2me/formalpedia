-- Prove2me | solution 1 for Malliavin.BrownianIteratedConstruction.inner_brownianPurePowerIntegral_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:37:36.20059+00:00
-- url     : https://prove2.me/submissions/db92d124-1e7f-4463-8075-42fa9066c3c3

import Definitions.Def_Malliavin_IteratedKernelPurePower
import Definitions.Def_Malliavin_BrownianPolynomialHermite
import Definitions.Def_Malliavin_BrownianPurePowerIntegral
import Theorems.Thm_Malliavin_BrownianIteratedConstruction_inner_brownianMultipleIntegralCLM_of_ne


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
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {m n : ℕ} (hmn : m ≠ n)
    (f g : Lp ℝ 2 nonnegativeLebesgueMeasure) :
    inner ℝ (brownianPurePowerIntegral hB m f)
      (brownianPurePowerIntegral hB n g) = 0 := by
  exact inner_brownianMultipleIntegralCLM_of_ne hB hsm hmn
    (iteratedKernelPurePower m f) (iteratedKernelPurePower n g)
end Malliavin.BrownianIteratedConstruction
