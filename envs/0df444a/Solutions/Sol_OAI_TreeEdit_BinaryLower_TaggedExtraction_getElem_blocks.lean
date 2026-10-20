-- Prove2me | solution 1 for OAI.TreeEdit.BinaryLower.TaggedExtraction.getElem_blocks
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T18:48:50.799143+00:00
-- url     : https://prove2.me/submissions/3febe5c5-24f3-4512-ad64-313cc18ce88a

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/BinaryEdit/TaggedExtraction.lean:L54-L71
-- (upload_full_project.md Phase 4): solution for node OAI.TreeEdit.BinaryLower.TaggedExtraction.getElem_blocks. The node keeps its source
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

-- ---- from OAI.Combinatorics.BinaryEdit.TaggedExtraction ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem dite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t : c → α} {e : ¬c → α} : (dite c t e) = e hc := @dif_neg c h hc α t e

namespace OAI

noncomputable section
namespace TreeEdit.BinaryLower
namespace TaggedExtraction

universe u
variable {α : Type u}

/-- Indexing a concatenated row at block `i` and within-block position `j`. -/
lemma getElem_blocks {m B : ℕ} (X : Fin m → Word α B) (i : Fin m) (j : Fin B) :
    (blocks X)[i.val * B + j.val]'(by rw [length_blocks]; exact block_index_lt i j) =
      (X i).val[j.val]'(by rw [(X i).property]; exact j.isLt) := by
  induction m with
  | zero => exact Fin.elim0 i
  | succ m ih =>
    refine Fin.cases ?_ (fun i => ?_) i
    · simp [blocks_succ, (X 0).property, j.isLt]
    · have hlo : B ≤ (i.val + 1) * B + j.val := by
        calc
          B ≤ (i.val + 1) * B := Nat.le_mul_of_pos_left B (Nat.succ_pos _)
          _ ≤ (i.val + 1) * B + j.val := Nat.le_add_right _ _
      have he : (i.val + 1) * B + j.val - B = i.val * B + j.val := by
        simp only [Nat.add_mul, Nat.one_mul]
        omega
      simpa only [Fin.val_succ, blocks_succ, List.getElem_append, (X 0).property,
        dite_eq_right (Nat.not_lt.mpr hlo), he] using ih (fun i => X i.succ) i

end TaggedExtraction
end TreeEdit.BinaryLower

end

end OAI

-- ---- platform node ----
open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower OAI.TreeEdit.BinaryLower.TaggedExtraction


theorem solution.{u} : type_of% @_root_.OAI.TreeEdit.BinaryLower.TaggedExtraction.getElem_blocks.{u} := @_root_.OAI.TreeEdit.BinaryLower.TaggedExtraction.getElem_blocks.{u}
