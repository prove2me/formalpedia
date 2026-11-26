-- Prove2me | solution 1 for Malliavin.BrownianIteratedConstruction.inner_brownianMultipleIntegralCLM_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:23:07.169821+00:00
-- url     : https://prove2.me/submissions/89b4352c-c996-48ed-97dc-d4cf9c49e978

import Definitions.Def_Malliavin_BrownianChaosHilbertSum
import Definitions.Def_Malliavin_BrownianMultipleIntegral
import Theorems.Thm_Malliavin_BrownianIteratedConstruction_brownianMultipleIntegralCLM_apply

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
    {m n : ℕ} (hmn : m ≠ n) (f : IteratedKernel m) (g : IteratedKernel n) :
    inner ℝ (brownianMultipleIntegralCLM hB m f)
      (brownianMultipleIntegralCLM hB n g) = 0 := by
  rw [brownianMultipleIntegralCLM_apply, brownianMultipleIntegralCLM_apply,
    real_inner_smul_left, real_inner_smul_right,
    integralCLM_differentOrder hB hsm positiveOrderedBoxDense hmn, mul_zero, mul_zero]
end Malliavin.BrownianIteratedConstruction
