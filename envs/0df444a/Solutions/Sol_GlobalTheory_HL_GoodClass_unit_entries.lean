-- Prove2me | solution 1 for GlobalTheory.HL.GoodClass.unit_entries
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:35:16.602004+00:00
-- url     : https://prove2.me/submissions/75c226c6-f274-4659-87f5-7238d97a1400

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SpanToLePerp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FramesCommonStabiliserEqPairingMatrixStabiliser
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetFrameClassProperties
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_UnitEntries
import Theorems.Thm_GlobalTheory_HL_GoodClass_UnitIn_cancel
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_FrameBasic_sig_cons
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
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.GoodClass
open GlobalTheory.FrameBasic
variable {E : Type} [CommRing E]
namespace GlobalTheory.HL.GoodClass
theorem _root_.solution (O : Subring E) (hO : ∀ (x : E) (s : ℕ), 0 < s → x ^ s ∈ O → x ∈ O) :
    ∀ bs : List (Eˣ × ℕ+), (∀ l ≤ (bs.map (fun b => (b.2 : ℕ))).sum, (∀ a < l, sig bs a < l) →
      UnitIn O (∏ a ∈ Finset.range l, ptEntryL bs a (sig bs a))) →
      ∀ a < (bs.map (fun b => (b.2 : ℕ))).sum, UnitIn O (ptEntryL bs a (sig bs a))
  | [], _, a, h => by simp at h
  | (t, s) :: bs, H, a, h => by
    simp only [List.map_cons, List.sum_cons] at h H
    have e1 : ∀ c < (s : ℕ), ptEntryL ((t, s) :: bs) c (sig ((t, s) :: bs) c) = t := by
      intro c hc
      simp only [sig_cons, ptEntryL, hc, if_true]
      rw [if_pos ⟨trivial, by omega⟩, if_pos (by omega)]
    have e2 : ∀ c, ptEntryL ((t, s) :: bs) (s + c) (sig ((t, s) :: bs) (s + c)) =
        ptEntryL bs c (sig bs c) := by
      intro c
      have hc : ¬ ((s : ℕ) + c < s) := by omega
      simp only [sig_cons, ptEntryL, hc, if_false, false_and, Nat.add_sub_cancel_left]
      rw [if_pos ⟨by omega, by omega⟩]
    have h1 := H s (by omega) (fun c hc => by simp only [sig_cons, hc, if_true]; omega)
    by_cases ha : a < s
    · rw [Finset.prod_congr rfl (fun c hc => e1 c (Finset.mem_range.1 hc)), Finset.prod_const,
        Finset.card_range] at h1
      obtain ⟨h2, y, hy, hy1⟩ := h1
      rw [e1 a ha]
      refine ⟨hO _ _ s.pos h2, ((t⁻¹ : Eˣ) : E), hO _ _ s.pos ?_, t.mul_inv⟩
      have : ((t⁻¹ : Eˣ) : E) ^ (s : ℕ) = y := by
        rw [← mul_one (_ ^ _), ← hy1, ← mul_assoc, ← mul_pow, t.inv_mul, one_pow, one_mul]
      rwa [this]
    · obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le (not_lt.1 ha)
      rw [e2]
      refine solution O hO bs (fun l hl hs => ?_) c (by omega)
      have h2 := H (s + l) (by omega) (fun c hc => by
        simp only [sig_cons]
        split_ifs with h3
        · omega
        · have := hs (c - s) (by omega); omega)
      rw [Finset.prod_range_add] at h2
      simp only [e2] at h2
      exact h1.cancel h2
end GlobalTheory.HL.GoodClass
