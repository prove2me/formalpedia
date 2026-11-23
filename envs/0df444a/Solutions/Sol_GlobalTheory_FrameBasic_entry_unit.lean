-- Prove2me | solution 1 for GlobalTheory.FrameBasic.entry_unit
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:59:26.43732+00:00
-- url     : https://prove2.me/submissions/da9c9b9b-d00f-423f-bb81-ed40fddd253f

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Theorems.Thm_GlobalTheory_FrameBasic_sig_cons
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
noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical TensorProduct
open GlobalTheory GlobalTheory.FrameBasic
variable {E : Type} [CommRing E]
namespace GlobalTheory.FrameBasic
theorem _root_.solution : ∀ (bs : List (Eˣ × ℕ+)) (a : ℕ), a < (bs.map (fun b => (b.2 : ℕ))).sum →
    sig bs a < (bs.map (fun b => (b.2 : ℕ))).sum ∧ IsUnit (ptEntryL bs a (sig bs a))
  | [], a, h => by simp at h
  | (t, s) :: bs, a, h => by
    simp only [List.map_cons, List.sum_cons] at h ⊢
    by_cases h1 : a < s
    · simp only [sig_cons, ptEntryL, h1, if_true]
      refine ⟨by omega, ?_⟩
      rw [if_pos ⟨trivial, by omega⟩, if_pos (by omega)]
      exact t.isUnit
    · obtain ⟨h2, h3⟩ := solution bs (a - s) (by omega)
      simp only [sig_cons, ptEntryL, h1, if_false, false_and]
      refine ⟨by omega, ?_⟩
      rw [if_pos ⟨by omega, by omega⟩, Nat.add_sub_cancel_left]
      exact h3
end GlobalTheory.FrameBasic
