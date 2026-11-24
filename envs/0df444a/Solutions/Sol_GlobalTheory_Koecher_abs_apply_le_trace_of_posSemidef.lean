-- Prove2me | solution 1 for GlobalTheory.Koecher.abs_apply_le_trace_of_posSemidef
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:36:28.83387+00:00
-- url     : https://prove2.me/submissions/532dbb4f-a1f7-428f-a906-3be6cfd32bf0

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
theorem _root_.solution {g : ℕ} {T : Matrix (Fin g) (Fin g) ℝ}
    (hT : T.PosSemidef) (i j : Fin g) : |T i j| ≤ T.trace := by
  have hd : ∀ k, T k k ≤ T.trace := fun k =>
    Finset.single_le_sum (f := fun k => T k k) (fun k _ => hT.diag_nonneg) (Finset.mem_univ k)
  have hs : T j i = T i j := by simpa using hT.1.apply i j
  have h1 := hT.dotProduct_mulVec_nonneg (Pi.single i 1 + Pi.single j 1)
  have h2 := hT.dotProduct_mulVec_nonneg (Pi.single i 1 - Pi.single j 1)
  simp only [star_trivial, mulVec_add, mulVec_sub, add_dotProduct, sub_dotProduct, dotProduct_add,
    dotProduct_sub, single_dotProduct, mulVec_single_one, col_apply, one_mul, hs] at h1 h2
  have := hd i
  have := hd j
  rw [abs_le]
  constructor <;> linarith
end GlobalTheory.Koecher
