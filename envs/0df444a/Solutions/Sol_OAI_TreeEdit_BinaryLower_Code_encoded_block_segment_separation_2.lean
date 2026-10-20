-- Prove2me | solution 2 for OAI.TreeEdit.BinaryLower.Code.encoded_block_segment_separation
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T21:28:05.492995+00:00
-- url     : https://prove2.me/submissions/81c9d615-e237-4b38-8cd6-f0faec9e1986

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/BinaryEdit/EncodedSegmentSeparation.lean:L11-L46
-- (upload_full_project.md Phase 4): solution for node OAI.TreeEdit.BinaryLower.Code.encoded_block_segment_separation. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
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

-- ---- from OAI.Combinatorics.BinaryEdit.EncodingIndex ----
namespace OAI

/-! Indexing fixed-width concatenated codewords. -/
namespace TreeEdit.BinaryLower

universe u v
variable {α : Type u} {β : Type v} {P : ℕ}

/-- A block-coordinate lookup in the actual concatenation extension. -/
theorem getElem?_encode_block (c : α → Word β P) (x : List α)
    (i j : ℕ) (hi : i < x.length) (hj : j < P) :
    (encode c x)[i * P + j]? = (c x[i]).val[j]? := by
  induction x generalizing i with
  | nil => simp only [List.length_nil] at hi; omega
  | cons a x ih =>
      cases i with
      | zero =>
          simp only [Nat.zero_mul, Nat.zero_add, List.getElem_cons_zero, encode,
            List.flatMap_cons]
          exact List.getElem?_append_left (by simpa only [(c a).property] using hj)
      | succ i =>
          have hi' : i < x.length := by simpa only [List.length_cons, Nat.succ_lt_succ_iff] using hi
          simp only [encode, List.flatMap_cons, List.getElem_cons_succ]
          rw [List.getElem?_append_right (by rw [(c a).property]; simp only [Nat.add_mul, Nat.one_mul]; omega)]
          rw [(c a).property]
          have heq : (i + 1) * P + j - P = i * P + j := by
            simp only [Nat.add_mul, Nat.one_mul]
            omega
          rw [heq]
          exact ih i hi'

/-- A segment wholly contained in one encoded block is exactly the
corresponding segment of that codeword. -/
theorem encode_segment_eq (c : α → Word β P) (x : List α)
    (i j a : ℕ) (hi : i < x.length) (hja : j + a ≤ P) :
    ((encode c x).drop (i * P + j)).take a =
      (((c x[i]).val).drop j).take a := by
  apply List.ext_getElem?
  intro k
  by_cases hk : k < a
  · have hjk : j + k < P := by omega
    simpa only [List.getElem?_take, hk, ite_true, List.getElem?_drop,
      Nat.add_assoc] using getElem?_encode_block c x i (j + k) hi hjk
  · simp only [List.getElem?_take, hk, ite_false]

end TreeEdit.BinaryLower

end OAI

-- ---- from OAI.Combinatorics.BinaryEdit.EncodedSegmentSeparation ----
namespace OAI

namespace TreeEdit.BinaryLower.Code

universe u v

/-- Simultaneous separation of the actual codeword segments implies the
concrete within-block separation predicate used by unequal matching counts.
Optional lookup makes the bad-pair predicate total on natural block indices;
the predicate is only used at the explicitly valid indices in this theorem. -/
theorem encoded_block_segment_separation {α : Type u} {β : Type v}
    {M P a₀ : ℕ} (c : α → Word β P)
    (hsep : ∀ k l : α, k ≠ l → ∀ a i j : ℕ, a₀ ≤ a →
      i + a ≤ P → j + a ≤ P →
      100 * lcs (((c k).val.drop i).take a) (((c l).val.drop j).take a) ≤ 99 * a)
    (x y : List α) (hx : x.length = M) (hy : y.length = M) :
    BlockSegmentSeparation (encodedBit c x hx) (encodedBit c y hy)
      (fun b => x[b.1]? ≠ y[b.2]?) a₀ := by
  intro b hb hb₁ hb₂ i j a hi hi' hj hj' ha w hwx hwy
  have hb₁' : b.1 < x.length := by simpa only [hx] using hb₁
  have hb₂' : b.2 < y.length := by simpa only [hy] using hb₂
  have hletters : x[b.1] ≠ y[b.2] := by
    simpa only [List.getElem?_eq_getElem hb₁', List.getElem?_eq_getElem hb₂',
      ne_eq, Option.some.injEq] using hb
  have hioff : i - b.1 * P + a ≤ P := by
    simp only [Nat.add_mul, Nat.one_mul] at hi'
    omega
  have hjoff : j - b.2 * P + a ≤ P := by
    simp only [Nat.add_mul, Nat.one_mul] at hj'
    omega
  have heqx : ((encode c x).drop i).take a =
      (((c x[b.1]).val).drop (i - b.1 * P)).take a := by
    have h := encode_segment_eq c x b.1 (i - b.1 * P) a hb₁' hioff
    simpa only [Nat.add_sub_of_le hi] using h
  have heqy : ((encode c y).drop j).take a =
      (((c y[b.2]).val).drop (j - b.2 * P)).take a := by
    have h := encode_segment_eq c y b.2 (j - b.2 * P) a hb₂' hjoff
    simpa only [Nat.add_sub_of_le hj] using h
  rw [ofFn_encodedBit, heqx] at hwx
  rw [ofFn_encodedBit, heqy] at hwy
  exact (Nat.mul_le_mul_left 100 (length_le_lcs hwx hwy)).trans
    (hsep x[b.1] y[b.2] hletters a (i - b.1 * P) (j - b.2 * P) ha hioff hjoff)

end TreeEdit.BinaryLower.Code

end OAI

-- ---- platform node ----
open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower OAI.TreeEdit.BinaryLower.Code


theorem solution.{u,v} : type_of% @_root_.OAI.TreeEdit.BinaryLower.Code.encoded_block_segment_separation.{u,v} := @_root_.OAI.TreeEdit.BinaryLower.Code.encoded_block_segment_separation.{u,v}
