-- Prove2me | solution 1 for GlobalTheory.SgLoc.PtAlg.ptEntryL_append
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:35:31.790948+00:00
-- url     : https://prove2.me/submissions/78275470-ba93-4a3f-b23a-c3a94e569861

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_RowRawRange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SameBlockAppend
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
theorem _root_.solution (bs : List (Eˣ × ℕ+)) (t : Eˣ) (s : ℕ+) :
    ∀ (m : ℕ), (bs.map (fun b => (b.2 : ℕ))).sum = m → ∀ a b : ℕ,
      ptEntryL (bs ++ [(t, s)]) a b =
        if a < m ∧ b < m then ptEntryL bs a b
        else if m ≤ a ∧ m ≤ b ∧ a + b + 1 = 2 * m + s then (t : E) else 0 := by
  induction bs with
  | nil =>
    intro m hm a b
    simp only [List.map_nil, List.sum_nil] at hm
    subst hm
    simp only [List.nil_append, ptEntryL]
    split_ifs <;> first | rfl | omega
  | cons hd bs ih =>
    obtain ⟨t', s'⟩ := hd
    intro m hm a b
    simp only [List.map_cons, List.sum_cons] at hm
    simp only [List.cons_append, ptEntryL]
    rw [ih _ rfl]
    split_ifs <;> first | rfl | omega
end GlobalTheory.SgLoc.PtAlg
