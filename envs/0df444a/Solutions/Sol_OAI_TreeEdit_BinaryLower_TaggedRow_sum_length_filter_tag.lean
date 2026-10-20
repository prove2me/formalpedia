-- Prove2me | solution 1 for OAI.TreeEdit.BinaryLower.TaggedRow.sum_length_filter_tag
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T18:53:34.941155+00:00
-- url     : https://prove2.me/submissions/76fcee93-5c3b-4855-9eba-841954471bfb

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/BinaryEdit/TaggedRowLCS.lean:L60-L74
-- (upload_full_project.md Phase 4): solution for node OAI.TreeEdit.BinaryLower.TaggedRow.sum_length_filter_tag. The node keeps its source
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

-- ---- from OAI.Combinatorics.BinaryEdit.TaggedRowLCS ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-! Longest common subsequence bounds for rows over disjoint tagged alphabets. -/
namespace TreeEdit.BinaryLower.TaggedRow
open scoped BigOperators

/-- Tag fibers partition every finite word's positions. -/
theorem sum_length_filter_tag {α I : Type*} [Fintype I] [DecidableEq I]
    (tag : α → I) (z : List α) :
    (∑ i, (z.filter (fun a => decide (tag a = i))).length) = z.length := by
  induction z with
  | nil => simp
  | cons a z ih =>
    have heq : ∀ i, ((a :: z).filter (fun b => decide (tag b = i))).length =
        (if tag a = i then 1 else 0) +
          (z.filter (fun b => decide (tag b = i))).length := by
      intro i
      by_cases h : tag a = i <;> simp [h, Nat.add_comm]
    simp_rw [heq]
    rw [Finset.sum_add_distrib, ih]
    simp [Nat.add_comm]

end TreeEdit.BinaryLower.TaggedRow

end OAI

-- ---- platform node ----
open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower OAI.TreeEdit.BinaryLower.TaggedRow
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.TreeEdit.BinaryLower.TaggedRow.sum_length_filter_tag := @_root_.OAI.TreeEdit.BinaryLower.TaggedRow.sum_length_filter_tag
