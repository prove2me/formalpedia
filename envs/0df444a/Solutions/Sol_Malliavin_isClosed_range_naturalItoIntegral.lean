-- Prove2me | solution 1 for Malliavin.isClosed_range_naturalItoIntegral
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:52:37.628319+00:00
-- url     : https://prove2.me/submissions/98c5f23d-baca-4448-9af6-09c904a72b75

import Definitions.Def_Malliavin_ItoConstruction
import Definitions.Def_Malliavin_ItoConsequences

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
    IsClosed (LinearMap.range (naturalItoIntegral hB hsm hnat).toLinearMap :
      Set (RandomL2 P)) := by
  let : Fact (𝓅.predictable ≤
      (inferInstance : MeasurableSpace (ℝ≥0 × W))) :=
    ⟨predictable_le_prod 𝓅⟩
  exact (naturalItoIntegralIsometry hB hsm hnat).isometry.isClosedEmbedding.isClosed_range
end Malliavin
