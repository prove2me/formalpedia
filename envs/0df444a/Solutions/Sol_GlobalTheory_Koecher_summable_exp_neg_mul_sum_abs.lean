-- Prove2me | solution 1 for GlobalTheory.Koecher.summable_exp_neg_mul_sum_abs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:26:00.731917+00:00
-- url     : https://prove2.me/submissions/b456f259-4f0c-490d-bda5-f3854bbd8f5e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_GenMain
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_FourierCoeffUnitCubeTranslateOfEntirePeriodic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_SetIntegralPowEqZeroOfPosFreqEuclidean
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_SndFDerivAddSndFDerivIEqZeroOfHarmonicAtLine
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExistsNatMulQuadraticLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_NormLeTsumOfCubeFourierCoeffLe
import Theorems.Thm_GlobalTheory_summable_prod_tuples


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix Filter Topology MeasureTheory
open scoped BigOperators Real
open GlobalTheory
open GlobalTheory.Koecher
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G.Key
namespace GlobalTheory.Koecher
theorem _root_.solution {ι : Type*} [Fintype ι] {ε : ℝ} (hε : 0 < ε) :
    Summable fun m : ι → ℤ => Real.exp (-(ε * ∑ q, |(m q : ℝ)|)) := by
  have h0 : Summable fun n : ℕ => Real.exp (-(ε * n)) := by
    have := summable_geometric_of_lt_one (Real.exp_pos (-ε)).le
      (Real.exp_lt_one_iff.2 (by linarith))
    refine this.congr fun n => ?_
    rw [← Real.exp_nat_mul]; congr 1; ring
  have h1 : Summable fun n : ℤ => Real.exp (-(ε * |(n : ℝ)|)) :=
    Summable.of_nat_of_neg (by simpa using h0) (by simpa using h0)
  refine (summable_prod_tuples (J := fun _ : ι => ℤ)
    (u := fun _ n => Real.exp (-(ε * |(n : ℝ)|))) (fun _ _ => (Real.exp_pos _).le)
    fun _ => h1).congr fun m => ?_
  rw [← Real.exp_sum, Finset.mul_sum, Finset.sum_neg_distrib]
end GlobalTheory.Koecher
