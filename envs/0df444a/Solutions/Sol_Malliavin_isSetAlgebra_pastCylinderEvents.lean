-- Prove2me | solution 1 for Malliavin.isSetAlgebra_pastCylinderEvents
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:47:58.447726+00:00
-- url     : https://prove2.me/submissions/559d6670-7396-4b16-88f0-dafa63bce928

import Definitions.Def_Malliavin_NaturalClarkOcone
import Mathlib.MeasureTheory.Constructions.Cylinders
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Definitions.Def_Malliavin_PastCylinderDensity

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
noncomputable section
open Malliavin
variable {E F W : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
variable [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
  {B : ℝ≥0 → W → ℝ}
omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    [MeasurableSpace W] [BorelSpace W] [SecondCountableTopology W]
namespace Malliavin
theorem _root_.solution (B : ℝ≥0 → W → ℝ) (a : ℝ≥0) :
    IsSetAlgebra (pastCylinderEvents B a) where
  empty_mem := by
    exact ⟨∅, empty_mem_measurableCylinders _, Set.preimage_empty⟩
  compl_mem := by
    rintro s ⟨C, hC, rfl⟩
    exact ⟨Cᶜ, compl_mem_measurableCylinders hC, Set.preimage_compl⟩
  union_mem := by
    rintro s t ⟨C, hC, rfl⟩ ⟨D, hD, rfl⟩
    exact ⟨C ∪ D, union_mem_measurableCylinders hC hD, Set.preimage_union⟩
end Malliavin
