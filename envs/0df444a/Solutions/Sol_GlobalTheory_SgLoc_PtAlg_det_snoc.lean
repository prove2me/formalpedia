-- Prove2me | solution 1 for GlobalTheory.SgLoc.PtAlg.det_snoc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:02:16.480719+00:00
-- url     : https://prove2.me/submissions/eaebd266-4f1e-412d-ab6d-c9dda6283bec

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_RowRawRange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SameBlockAppend
import Theorems.Thm_GlobalTheory_SgLoc_PtAlg_det_snoc_eq
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
open ValuativeRel MeasureTheory ComplexConjugate Formalism.MainNotions.S.Loc GlobalTheory.SgLoc
open scoped ComplexOrder
open GlobalTheory GlobalTheory.SgLoc GlobalTheory.SgLoc.PtAlg
variable {E : Type} [CommRing E]
namespace GlobalTheory.SgLoc.PtAlg
theorem _root_.solution {m : ℕ} (h : Pt E m) (t : Eˣ) (s : ℕ+) :
    (h.snoc t s).mat.det = h.mat.det * (t : E) ^ (s : ℕ) ∨
      (h.snoc t s).mat.det = -(h.mat.det * (t : E) ^ (s : ℕ)) := by
  rw [det_snoc_eq]
  rcases Int.units_eq_one_or (Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin s))) with h1 | h1
  · left
    rw [h1]
    simp
  · right
    rw [h1]
    simp
end GlobalTheory.SgLoc.PtAlg
