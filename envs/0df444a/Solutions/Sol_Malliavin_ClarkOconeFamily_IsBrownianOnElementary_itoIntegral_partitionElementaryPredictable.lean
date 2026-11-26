-- Prove2me | solution 1 for Malliavin.ClarkOconeFamily.IsBrownianOnElementary.itoIntegral_partitionElementaryPredictable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:03:06.7923+00:00
-- url     : https://prove2.me/submissions/be6a5945-a9ee-492c-ae31-f217a6c900b1

import Definitions.Def_Malliavin_ClarkOcone
import Definitions.Def_Malliavin_ElementaryIto

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
namespace Malliavin
namespace ClarkOconeFamily.IsBrownianOnElementary
theorem _root_.solution
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›} {C : ClarkOconeFamily B P 𝓕}
    (hC : C.IsBrownianOnElementary) {n : ℕ} (Q : Partition n)
    (Z : (i : Fin n) → lpMeas ℝ ℝ (𝓕 (Q.t i.castSucc)) 2 P) :
    C.itoIntegral (partitionElementaryPredictable Q Z) =
      C.partitionElementaryIntegralValue Q Z := by
  rw [partitionElementaryPredictable, partitionElementaryIntegralValue, map_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  exact hC (Q.mono.monotone (Fin.castSucc_le_succ i)) (Z i)
end ClarkOconeFamily.IsBrownianOnElementary
end Malliavin
