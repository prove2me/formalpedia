-- Prove2me | solution 1 for Malliavin.naturalMartingaleRepresentation_iff_centeredNaturalItoRange_orthogonal_eq_bot
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:55:06.053628+00:00
-- url     : https://prove2.me/submissions/fc0dd13d-4692-4ee3-b749-d690bb362a88

import Definitions.Def_Malliavin_ItoConsequences
import Definitions.Def_Malliavin_NaturalItoRange
import Theorems.Thm_Malliavin_naturalMartingaleRepresentation_iff_centeredNaturalItoRange_eq_top

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
      (centeredNaturalItoRange hB hsm hnat)ᗮ = ⊥ := by
  let _ : CompleteSpace (centeredNaturalItoRange hB hsm hnat) :=
    (isClosed_centeredNaturalItoRange hB hsm hnat).completeSpace_coe
  rw [naturalMartingaleRepresentation_iff_centeredNaturalItoRange_eq_top]
  exact Submodule.orthogonal_eq_bot_iff.symm
end Malliavin
