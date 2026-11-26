-- Prove2me | solution 1 for Malliavin.naturalMartingaleRepresentation_canonical
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:58:17.598709+00:00
-- url     : https://prove2.me/submissions/5694fb15-e834-451a-9b32-8d8965c4ffaf

import Definitions.Def_Malliavin_ItoConsequences
import Definitions.Def_Malliavin_NaturalItoRange
import Theorems.Thm_Malliavin_centeredNaturalItoIntegral_bestNaturalItoIntegrand

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
    (hnat : 𝓅 = Filtration.natural B hsm)
    (hMRT : NaturalMartingaleRepresentation hB hsm hnat)
    (G : RandomL2 P) :
    G = expectationL2 G +
      naturalItoIntegral hB hsm hnat
        (bestNaturalItoIntegrandOfRandom hB hsm hnat G) := by
  have h := centeredNaturalItoIntegral_bestNaturalItoIntegrand
    hB hsm hnat hMRT (centeredPartL2 G)
  have hambient := congrArg Subtype.val h
  change naturalItoIntegral hB hsm hnat
    (bestNaturalItoIntegrandOfRandom hB hsm hnat G) =
      G - expectationL2 G at hambient
  rw [hambient]
  abel
end Malliavin
