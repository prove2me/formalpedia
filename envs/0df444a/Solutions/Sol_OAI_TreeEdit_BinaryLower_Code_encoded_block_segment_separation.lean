-- Prove2me | solution 1 for OAI.TreeEdit.BinaryLower.Code.encoded_block_segment_separation
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T18:23:42.912683+00:00
-- url     : https://prove2.me/submissions/851a78ad-de10-4c41-9c2d-197b8f2f2e36

import Mathlib
import Definitions.Def_BinaryEditLower
import Definitions.Def_OAI_Combinatorics_TreeEdit_Model__BinaryEditLower
import Definitions.Def_OAI_Combinatorics_BinaryEdit_Model
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteTreeWords
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteTreeGeometry
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteVectors
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteVectorRestrictions
import Definitions.Def_OAI_Combinatorics_BinaryEdit_WordFinite
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteTreeInstantiation
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteTreeTags
import Definitions.Def_OAI_Combinatorics_BinaryEdit_TaggedGaps
import Definitions.Def_OAI_Combinatorics_BinaryEdit_TaggedNonsplit
import Definitions.Def_OAI_Combinatorics_TreeEdit_EditMetric__BinaryEditLower
import Definitions.Def_OAI_Combinatorics_TreeEdit_Alignments__BinaryEditLower
import Definitions.Def_OAI_Combinatorics_BinaryEdit_LCS
import Definitions.Def_OAI_Combinatorics_BinaryEdit_TaggedExtraction
import Definitions.Def_OAI_Combinatorics_BinaryEdit_BlockExtraction
import Definitions.Def_OAI_Combinatorics_BinaryEdit_TaggedRowLCS
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteSeparation
import Definitions.Def_OAI_Combinatorics_BinaryEdit_Branching
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteActivityBridge
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteFourier
import Definitions.Def_OAI_Combinatorics_BinaryEdit_ScalarCutsBool
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteCoordinates
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteWordDetection
import Definitions.Def_OAI_Combinatorics_BinaryEdit_CheapTranslations
import Definitions.Def_OAI_Combinatorics_BinaryEdit_Distortion
import Definitions.Def_OAI_Combinatorics_BinaryEdit_EditMetric
import Definitions.Def_OAI_Combinatorics_BinaryEdit_ParameterImage
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteParameters
import Definitions.Def_OAI_Combinatorics_BinaryEdit_EncodedImage
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteFamilyTransfer
import Definitions.Def_OAI_Combinatorics_BinaryEdit_CodeNumerics
import Definitions.Def_OAI_Combinatorics_BinaryEdit_RandomMatching
import Definitions.Def_OAI_Combinatorics_BinaryEdit_SegmentMatchingCount
import Definitions.Def_OAI_Combinatorics_BinaryEdit_CodeUnionBound
import Definitions.Def_OAI_Combinatorics_BinaryEdit_SegmentCode
import Definitions.Def_OAI_Combinatorics_BinaryEdit_CodeAdditive
import Definitions.Def_OAI_Combinatorics_BinaryEdit_MatchingSpanBudget
import Definitions.Def_OAI_Combinatorics_BinaryEdit_MatchingSegments
import Definitions.Def_OAI_Combinatorics_BinaryEdit_UnequalSegments

open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower OAI.TreeEdit.BinaryLower.Code
universe u v
theorem h49_enc_window {α : Type u} {β : Type v} {P : ℕ} (c : α → Word β P) :
    ∀ (x : List α) (b : ℕ) (hb : b < x.length) (i' a : ℕ), i' + a ≤ P →
    ((encode c x).drop (b*P+i')).take a = ((c (x[b])).val.drop i').take a := by
  intro x
  induction x with
  | nil => intro b hb; simp at hb
  | cons h t ih =>
    intro b hb i' a hia
    have hl : (c h).val.length = P := (c h).2
    have he : encode c (h :: t) = (c h).val ++ encode c t := by simp [encode]
    rw [he]
    rcases b with _ | b
    · simp only [zero_mul, zero_add, List.getElem_cons_zero]
      rw [List.drop_append_of_le_length (by omega), List.take_append_of_le_length (by simp; omega)]
    · simp only [List.getElem_cons_succ]
      rw [show (b+1)*P + i' = (c h).val.length + (b*P + i') by rw [hl]; ring, List.drop_append,
        List.drop_eq_nil_of_le (by omega), List.nil_append, Nat.add_sub_cancel_left]
      exact ih b (by simp at hb; omega) i' a hia

theorem solution {α : Type u} {β : Type v}
    {M P a₀ : ℕ} (c : α → Word β P)
    (hsep : ∀ k l : α, k ≠ l → ∀ a i j : ℕ, a₀ ≤ a →
      i + a ≤ P → j + a ≤ P →
      100 * lcs (((c k).val.drop i).take a) (((c l).val.drop j).take a) ≤ 99 * a)
    (x y : List α) (hx : x.length = M) (hy : y.length = M) :
    BlockSegmentSeparation (encodedBit c x hx) (encodedBit c y hy)
      (fun b => x[b.1]? ≠ y[b.2]?) a₀ := by
  intro b hbad hb1 hb2 i j a hi1 hi2 hj1 hj2 ha w hwx hwy
  rw [ofFn_encodedBit] at hwx hwy
  have hxl : b.1 < x.length := by omega
  have hyl : b.2 < y.length := by omega
  have hne : x[b.1] ≠ y[b.2] := by
    intro h; apply hbad
    rw [List.getElem?_eq_getElem hxl, List.getElem?_eq_getElem hyl, h]
  obtain ⟨i', rfl⟩ : ∃ i', i = b.1 * P + i' := ⟨i - b.1 * P, by omega⟩
  obtain ⟨j', rfl⟩ : ∃ j', j = b.2 * P + j' := ⟨j - b.2 * P, by omega⟩
  have hi' : i' + a ≤ P := by nlinarith
  have hj' : j' + a ≤ P := by nlinarith
  rw [h49_enc_window c x b.1 hxl i' a hi'] at hwx
  rw [h49_enc_window c y b.2 hyl j' a hj'] at hwy
  have := hsep _ _ hne a i' j' ha hi' hj'
  have hw := length_le_lcs hwx hwy
  omega

