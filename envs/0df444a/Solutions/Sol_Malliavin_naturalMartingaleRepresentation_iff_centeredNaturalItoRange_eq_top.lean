-- Prove2me | solution 1 for Malliavin.naturalMartingaleRepresentation_iff_centeredNaturalItoRange_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:54:05.254578+00:00
-- url     : https://prove2.me/submissions/a882adbe-ac41-4d06-baf3-0e9b47e502a6

import Definitions.Def_Malliavin_ItoConsequences
import Definitions.Def_Malliavin_NaturalItoRange

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
noncomputable section
open Malliavin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
  {B : ℝ≥0 → W → ℝ}
omit [CompleteSpace W] [BorelSpace W]
namespace Malliavin
theorem _root_.solution
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓅 = Filtration.natural B hsm) :
    NaturalMartingaleRepresentation hB hsm hnat ↔
      centeredNaturalItoRange hB hsm hnat = ⊤ := by
  rw [naturalMartingaleRepresentation_iff_surjective]
  exact LinearMap.range_eq_top.symm
end Malliavin
