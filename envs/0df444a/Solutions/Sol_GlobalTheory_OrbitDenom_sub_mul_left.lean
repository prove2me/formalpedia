-- Prove2me | solution 1 for GlobalTheory.OrbitDenom.sub_mul_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:12:24.116795+00:00
-- url     : https://prove2.me/submissions/94986cc9-bf41-4140-bd71-9ac80ccace58

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsEqZpowMulUnit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LeadingMinorsProdDenominatorUnitriangularFactors
import Theorems.Thm_GlobalTheory_OrbitDenom_sum_castLE
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.OrbitDenom
variable {E : Type} [CommRing E]
namespace GlobalTheory.OrbitDenom
theorem _root_.solution {n l : ℕ} (h : l ≤ n) {α : Type} (p : α → Fin n) (M N : Matrix (Fin n) (Fin n) E)
    (hM : ∀ a k : Fin n, a < k → M a k = 0) :
    (M * N).submatrix (Fin.castLE h) p =
      M.submatrix (Fin.castLE h) (Fin.castLE h) * N.submatrix (Fin.castLE h) p := by
  ext a b
  simp only [Matrix.submatrix_apply, Matrix.mul_apply]
  refine sum_castLE h (fun k => M (Fin.castLE h a) k * N k (p b)) ?_
  intro k hk
  rw [hM _ k (by rw [Fin.lt_def]; have := a.2; simp; omega), zero_mul]
end GlobalTheory.OrbitDenom
