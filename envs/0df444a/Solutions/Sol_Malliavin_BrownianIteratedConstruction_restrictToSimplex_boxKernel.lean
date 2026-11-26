-- Prove2me | solution 1 for Malliavin.BrownianIteratedConstruction.restrictToSimplex_boxKernel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:52:19.379899+00:00
-- url     : https://prove2.me/submissions/eb091600-7cd5-4f20-956e-8bdce56b20fd

import Definitions.Def_Malliavin_ItoConstruction
import Definitions.Def_Malliavin_BrownianIterated

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
omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [MeasurableSpace W]
    [BorelSpace W] [SecondCountableTopology W] [IsGaussian P]
namespace Malliavin.BrownianIteratedConstruction
theorem _root_.solution {n : ℕ} (a : OrderedBoxIndex n) :
    restrictToSimplex n (boxKernel a.u a.v) = orderedBoxSimplexKernel a := by
  apply Lp.ext
  unfold boxKernel orderedBoxSimplexKernel
  filter_upwards [restrictToSimplex_ae n _,
    ae_restrict_of_ae (indicatorConstLp_coeFn (p := 2) (μ := iteratedKernelMeasure n)
      (hs := measurableSet_orderedBox a.u a.v) (c := (1 : ℝ))),
    (indicatorConstLp_coeFn (p := 2)
      (μ := (iteratedKernelMeasure n).restrict (simplex ℝ≥0 n))
      (hs := measurableSet_orderedBox a.u a.v) (c := (1 : ℝ)))]
      with t hrestrict hfull hsimp
  exact hrestrict.trans (hfull.trans hsimp.symm)
end Malliavin.BrownianIteratedConstruction
