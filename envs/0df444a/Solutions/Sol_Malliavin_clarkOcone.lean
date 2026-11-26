-- Prove2me | solution 1 for Malliavin.clarkOcone
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:32:28.450926+00:00
-- url     : https://prove2.me/submissions/4dfca6e9-1180-4f9c-8f65-146645207202

import Definitions.Def_Malliavin_TimeDerivative
import Mathlib.Probability.Process.Predictable
import Definitions.Def_Malliavin_ClarkOcone
import Theorems.Thm_Malliavin_eq_predictableDerivative_of_representation

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9
noncomputable section
open Malliavin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
  {B : ℝ≥0 → W → ℝ}
namespace Malliavin
theorem _root_.solution {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (C : ClarkOconeFamily B P 𝓕) (F : D12 P) :
    F.1 = expectationL2 F.1 + clarkOconeIntegral C F :=
  by
    obtain ⟨u, hu⟩ := C.martingaleRepresentation F.1
    have hu_eq := eq_predictableDerivative_of_representation C F u hu
    calc
      F.1 = expectationL2 F.1 + C.itoIntegral u := hu
      _ = expectationL2 F.1 + C.itoIntegral (predictableDerivative C F) := by rw [hu_eq]
      _ = expectationL2 F.1 + clarkOconeIntegral C F := rfl
end Malliavin
