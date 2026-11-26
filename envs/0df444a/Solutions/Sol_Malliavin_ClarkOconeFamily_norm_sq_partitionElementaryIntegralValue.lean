-- Prove2me | solution 1 for Malliavin.ClarkOconeFamily.norm_sq_partitionElementaryIntegralValue
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:34:18.632361+00:00
-- url     : https://prove2.me/submissions/0e0d0d31-c9dd-4df4-8e03-02ce1bb08b0d

import Definitions.Def_Malliavin_ClarkOcone
import Definitions.Def_Malliavin_ElementaryIto
import Theorems.Thm_Malliavin_ClarkOconeFamily_inner_partitionElementaryIntegralValue

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
namespace ClarkOconeFamily
theorem _root_.solution
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›} (C : ClarkOconeFamily B P 𝓕)
    {n : ℕ} (Q : Partition n)
    (Z : (i : Fin n) → lpMeas ℝ ℝ (𝓕 (Q.t i.castSucc)) 2 P) :
    ‖C.partitionElementaryIntegralValue Q Z‖ ^ 2 =
      ‖partitionElementaryPredictable Q Z‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq]
  exact C.inner_partitionElementaryIntegralValue Q Z Z
end ClarkOconeFamily
end Malliavin
