-- Prove2me | solution 1 for GlobalTheory.Koecher.sum_mul_nonneg_of_posSemidef
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:36:31.431161+00:00
-- url     : https://prove2.me/submissions/1ebcdbb8-ab60-4334-b6b0-e7b69fe1d491

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_GenMain
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_FourierCoeffUnitCubeTranslateOfEntirePeriodic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_SetIntegralPowEqZeroOfPosFreqEuclidean
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_SndFDerivAddSndFDerivIEqZeroOfHarmonicAtLine
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExistsNatMulQuadraticLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_NormLeTsumOfCubeFourierCoeffLe

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
theorem _root_.solution {g : ℕ} {T P : Matrix (Fin g) (Fin g) ℝ}
    (hT : T.PosSemidef) (hP : P.PosSemidef) : 0 ≤ ∑ q : Fin g × Fin g, T q.1 q.2 * P q.1 q.2 := by
  have h := (hT.hadamard hP).dotProduct_mulVec_nonneg fun _ => 1
  simpa [dotProduct, mulVec, Fintype.sum_prod_type] using h
end GlobalTheory.Koecher
