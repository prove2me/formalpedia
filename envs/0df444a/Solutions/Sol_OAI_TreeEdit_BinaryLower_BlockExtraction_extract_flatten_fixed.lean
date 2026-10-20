-- Prove2me | solution 1 for OAI.TreeEdit.BinaryLower.BlockExtraction.extract_flatten_fixed
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T18:52:08.523511+00:00
-- url     : https://prove2.me/submissions/9dd4fcc5-be5c-4f16-b1cf-d02828f7e073

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/BinaryEdit/BlockExtraction.lean:L22-L41
-- (upload_full_project.md Phase 4): solution for node OAI.TreeEdit.BinaryLower.BlockExtraction.extract_flatten_fixed. The node keeps its source
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

-- ---- from OAI.Combinatorics.BinaryEdit.BlockExtraction ----
namespace OAI

/-! Exact contiguous-window extraction from fixed-width block concatenations. -/

namespace TreeEdit.BinaryLower
namespace BlockExtraction

/-- The i-th fixed-width block is exactly the corresponding window of the
flattened list. This includes width zero. -/
theorem extract_flatten_fixed {α : Type*} (blocks : List (List α)) (B : ℕ)
    (hB : ∀ z ∈ blocks, z.length = B) (i : ℕ) (hi : i < blocks.length) :
    (blocks.flatten.drop (i * B)).take B = blocks[i] := by
  induction blocks generalizing i with
  | nil => simp at hi
  | cons z zs ih =>
      have hz : z.length = B := hB z (by simp)
      have hzs : ∀ t ∈ zs, t.length = B := fun t ht => hB t (by simp [ht])
      cases i with
      | zero =>
          simp only [Nat.zero_mul, List.drop_zero, List.flatten_cons, List.getElem_cons_zero]
          rw [← hz, List.take_left]
      | succ i =>
          have hi' : i < zs.length := by simpa using hi
          have hmul : (i + 1) * B = z.length + i * B := by rw [hz]; ring
          simp only [List.flatten_cons, List.getElem_cons_succ]
          rw [hmul, List.drop_length_add_append]
          exact ih hzs i hi'

end BlockExtraction
end TreeEdit.BinaryLower

end OAI

-- ---- platform node ----
open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower OAI.TreeEdit.BinaryLower.BlockExtraction


theorem solution : type_of% @_root_.OAI.TreeEdit.BinaryLower.BlockExtraction.extract_flatten_fixed := @_root_.OAI.TreeEdit.BinaryLower.BlockExtraction.extract_flatten_fixed
