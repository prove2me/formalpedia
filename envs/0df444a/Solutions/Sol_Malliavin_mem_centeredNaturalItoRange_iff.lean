-- Prove2me | solution 1 for Malliavin.mem_centeredNaturalItoRange_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:05:05.768655+00:00
-- url     : https://prove2.me/submissions/2d217a33-1459-4f9d-8091-ab89c2bbaba1

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
    (hnat : 𝓅 = Filtration.natural B hsm)
    (G : (CameronMartin.expectationMap P).ker) :
    G ∈ centeredNaturalItoRange hB hsm hnat ↔
      (G : RandomL2 P) ∈ naturalItoRange hB hsm hnat := by
  constructor
  · rintro ⟨U, hU⟩
    refine ⟨U, ?_⟩
    have h := congrArg Subtype.val hU
    change naturalItoIntegral hB hsm hnat U = (G : RandomL2 P) at h
    exact h
  · rintro ⟨U, hU⟩
    refine ⟨U, Subtype.ext ?_⟩
    change naturalItoIntegral hB hsm hnat U = (G : RandomL2 P)
    exact hU
end Malliavin
