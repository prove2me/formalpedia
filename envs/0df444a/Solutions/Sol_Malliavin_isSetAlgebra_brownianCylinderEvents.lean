-- Prove2me | solution 1 for Malliavin.isSetAlgebra_brownianCylinderEvents
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:53:27.546228+00:00
-- url     : https://prove2.me/submissions/c2bae232-582a-4a40-b7f9-9294d2e6580d

import Definitions.Def_Malliavin_PastCylinderDensity
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Definitions.Def_Malliavin_BrownianCylinderDensity

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open NormedSpace
open scoped ENNReal NNReal InnerProductSpace
noncomputable section
open Malliavin
variable {E W : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
variable [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
  {B : ℝ≥0 → W → ℝ}
omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    [MeasurableSpace W] [BorelSpace W] [SecondCountableTopology W]
namespace Malliavin
theorem _root_.solution (B : ℝ≥0 → W → ℝ) :
    IsSetAlgebra (brownianCylinderEvents B) where
  empty_mem := ⟨∅, empty_mem_measurableCylinders _, Set.preimage_empty⟩
  compl_mem := by
    rintro s ⟨C, hC, rfl⟩
    exact ⟨Cᶜ, compl_mem_measurableCylinders hC, Set.preimage_compl⟩
  union_mem := by
    rintro s t ⟨C, hC, rfl⟩ ⟨D, hD, rfl⟩
    exact ⟨C ∪ D, union_mem_measurableCylinders hC hD, Set.preimage_union⟩
end Malliavin
