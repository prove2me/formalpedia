-- Prove2me | solution 1 for GlobalTheory.HL.RStab.rmul_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:55:19.805199+00:00
-- url     : https://prove2.me/submissions/705720d6-543d-4075-835d-1b44405dc050

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NcardImageOfLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsIsometryNearIdentityCloseTuplesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsIsometryTupleMatrixRightMulNearIdentity
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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.RStab
namespace GlobalTheory.HL.RStab
theorem _root_.solution {E : Type} [CommRing E] {n m : ℕ} (x : Fin m → Fin n → E)
    (A : Matrix (Fin m) (Fin m) E) (a : Fin m) :
    rmul x A a - x a = ∑ i, (A i a - (1 : Matrix (Fin m) (Fin m) E) i a) • x i := by
  simp only [rmul, sub_smul, Finset.sum_sub_distrib]
  congr 1
  simp [Matrix.one_apply, ite_smul]
end GlobalTheory.HL.RStab
