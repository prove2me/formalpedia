-- Prove2me | solution 1 for OAI.TreeEdit.BinaryLower.TaggedRow.sum_deficit_le_row_deficit
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T18:54:59.851778+00:00
-- url     : https://prove2.me/submissions/18f00731-35da-4c3f-ac1e-a55c73057b2d

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/BinaryEdit/TaggedRowLCS.lean:L109-L128
-- (upload_full_project.md Phase 4): solution for node OAI.TreeEdit.BinaryLower.TaggedRow.sum_deficit_le_row_deficit. The node keeps its source
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
import Theorems.Thm_OAI_TreeEdit_BinaryLower_TaggedRow_sum_length_filter_tag

-- ---- from OAI.Combinatorics.BinaryEdit.TaggedRowLCS ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

/-! Longest common subsequence bounds for rows over disjoint tagged alphabets. -/
namespace TreeEdit.BinaryLower.TaggedRow
open scoped BigOperators

private theorem flatMap_single_index {I α : Type*} [DecidableEq I]
    (order : List I) (hn : order.Nodup) (i : I) (f : I → List α) :
    order.flatMap (fun j => if j = i then f j else []) =
      if i ∈ order then f i else [] := by
  induction order with
  | nil => simp
  | cons j order ih =>
    obtain ⟨hj, htail⟩ := List.nodup_cons.mp hn
    by_cases hji : j = i
    · subst j
      rw [List.flatMap_cons, ite_eq_left rfl, ih htail]
      simp [hj]
    · rw [List.flatMap_cons, ite_eq_right hji, List.nil_append, ih htail]
      simp only [List.mem_cons, Ne.symm hji, false_or]

theorem filter_row {α : Type*} {m : ℕ} (tag : α → Fin m)
    (blocks : Fin m → List α)
    (htags : ∀ j, ∀ a ∈ blocks j, tag a = j) (i : Fin m) :
    (row blocks).filter (fun a => decide (tag a = i)) = blocks i := by
  rw [row, List.filter_flatMap]
  have hb : ∀ j, (blocks j).filter (fun a => decide (tag a = i)) =
      if j = i then blocks j else [] := by
    intro j
    by_cases hji : j = i
    · subst j
      rw [ite_eq_left rfl]
      apply List.filter_eq_self.mpr
      intro a ha
      simp [htags i a ha]
    · simp only [ite_eq_right hji]
      apply List.filter_eq_nil_iff.mpr
      intro a ha
      simp [htags j a ha, hji]
  rw [List.flatMap_congr (fun j _ => hb j)]
  rw [flatMap_single_index _ (List.nodup_finRange m)]
  simp

/-- Common subsequences of rows are bounded by the sum of block LCS lengths. -/
theorem common_sublist_length_le_sum_lcs {α : Type*} {m : ℕ}
    (tag : α → Fin m) (X Y : Fin m → List α)
    (hX : ∀ i, ∀ a ∈ X i, tag a = i)
    (hY : ∀ i, ∀ a ∈ Y i, tag a = i)
    {z : List α} (hzX : z.Sublist (row X)) (hzY : z.Sublist (row Y)) :
    z.length ≤ ∑ i, lcs (X i) (Y i) := by
  rw [← sum_length_filter_tag tag z]
  apply Finset.sum_le_sum
  intro i _
  have hx := hzX.filter (fun a => decide (tag a = i))
  have hy := hzY.filter (fun a => decide (tag a = i))
  rw [filter_row tag X hX i] at hx
  rw [filter_row tag Y hY i] at hy
  exact length_le_lcs hx hy

/-- Local row bound used in the nonsplit-row argument. -/
theorem lcs_row_le_sum {α : Type*} {m : ℕ}
    (tag : α → Fin m) (X Y : Fin m → List α)
    (hX : ∀ i, ∀ a ∈ X i, tag a = i)
    (hY : ∀ i, ∀ a ∈ Y i, tag a = i) :
    lcs (row X) (row Y) ≤ ∑ i, lcs (X i) (Y i) := by
  apply csSup_le
  · exact ⟨0, [], by simp, by simp, rfl⟩
  · intro n hn
    obtain ⟨z, hzX, hzY, rfl⟩ := hn
    exact common_sublist_length_le_sum_lcs tag X Y hX hY hzX hzY

/-- Tagwise deficits accumulate in a single pair of rows. This is the
local deficit estimate consumed by the nonsplit-row counting argument. -/
theorem sum_deficit_le_row_deficit {α : Type*} {m B : ℕ}
    (tag : α → Fin m) (X Y : Fin m → List α)
    (hX : ∀ i, ∀ a ∈ X i, tag a = i)
    (hY : ∀ i, ∀ a ∈ Y i, tag a = i)
    (hXL : ∀ i, (X i).length = B) :
    (∑ i, deficit B (X i) (Y i)) ≤ deficit (m * B) (row X) (row Y) := by
  have hsplit : (∑ i, deficit B (X i) (Y i)) +
      (∑ i, lcs (X i) (Y i)) = m * B := by
    rw [← Finset.sum_add_distrib]
    have heq : ∀ i, deficit B (X i) (Y i) + lcs (X i) (Y i) = B := by
      intro i
      apply Nat.sub_add_cancel
      simpa [hXL i] using lcs_le_length_left (X i) (Y i)
    simp_rw [heq]
    simp
  have hlocal := lcs_row_le_sum tag X Y hX hY
  exact Nat.le_sub_of_add_le
    ((Nat.add_le_add_left hlocal _).trans_eq hsplit)

end TreeEdit.BinaryLower.TaggedRow

end OAI

-- ---- platform node ----
open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower OAI.TreeEdit.BinaryLower.TaggedRow
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.TreeEdit.BinaryLower.TaggedRow.sum_deficit_le_row_deficit := @_root_.OAI.TreeEdit.BinaryLower.TaggedRow.sum_deficit_le_row_deficit
