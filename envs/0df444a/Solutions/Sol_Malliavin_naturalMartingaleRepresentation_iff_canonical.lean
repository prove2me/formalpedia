-- Prove2me | solution 1 for Malliavin.naturalMartingaleRepresentation_iff_canonical
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:05:36.665651+00:00
-- url     : https://prove2.me/submissions/d0af5664-e922-4051-834c-9c261889195f

import Definitions.Def_Malliavin_ItoConsequences
import Definitions.Def_Malliavin_NaturalItoRange
import Theorems.Thm_Malliavin_naturalMartingaleRepresentation_canonical

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
      ∀ G : RandomL2 P,
        G = expectationL2 G + naturalItoIntegral hB hsm hnat
          (bestNaturalItoIntegrandOfRandom hB hsm hnat G) := by
  constructor
  · exact naturalMartingaleRepresentation_canonical hB hsm hnat
  · intro hCanonical G
    exact ⟨bestNaturalItoIntegrandOfRandom hB hsm hnat G, hCanonical G⟩
end Malliavin
