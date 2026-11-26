-- Prove2me | solution 1 for Malliavin.BrownianIteratedConstruction.brownianMultipleIntegralRange_isOrtho
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:47:45.868644+00:00
-- url     : https://prove2.me/submissions/151985cf-d907-4053-8534-c450d6473fde

import Definitions.Def_Malliavin_BrownianOrderedBoxDensity
import Definitions.Def_Malliavin_NaturalClarkOcone
import Definitions.Def_Malliavin_NaturalItoRange
import Definitions.Def_Malliavin_BrownianChaos

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
    {m n : ℕ} (hmn : m ≠ n) :
    brownianMultipleIntegralRange hB m ⟂ brownianMultipleIntegralRange hB n := by
  rw [Submodule.isOrtho_iff_inner_eq]
  rintro _ ⟨f, rfl⟩ _ ⟨g, rfl⟩
  exact integralCLM_differentOrder hB hsm positiveOrderedBoxDense hmn f g
end Malliavin.BrownianIteratedConstruction
