-- Prove2me | solution 1 for OAI.TreeEdit.get_encode_block
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T02:34:55.381386+00:00
-- url     : https://prove2.me/submissions/c7e2cdb1-570a-4467-963c-f6b03629c6dc

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/TreeEdit/SegmentComparison.lean:L48-L67
-- (upload_full_project.md Phase 4): solution for node OAI.TreeEdit.get_encode_block. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_TreeEdit
import Definitions.Def_OAI_Combinatorics_TreeEdit_Model
import Definitions.Def_OAI_Combinatorics_TreeEdit_FiniteProbability
import Definitions.Def_OAI_Combinatorics_TreeEdit_EditMetric
import Definitions.Def_OAI_Combinatorics_TreeEdit_Alignments
import Definitions.Def_OAI_Combinatorics_TreeEdit_SegmentComparison

-- ---- from OAI.Combinatorics.TreeEdit.SegmentComparison ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace TreeEdit

universe u

variable {α : Type u} {x y z : List α}

theorem get_encode_block {P : ℕ} (c : α → Word Bool P) (x : List α)
    (i r : ℕ) (hi : i < x.length) (hr : r < P) :
    (encode c x)[i * P + r]'(by
      rw [length_encode]
      have hh := Nat.mul_le_mul_right P (Nat.succ_le_of_lt hi)
      rw [Nat.succ_mul] at hh
      omega) = (c x[i]).val[r]'(by rw [(c x[i]).property]; exact hr) := by
  induction x generalizing i with
  | nil => simp at hi
  | cons a x ih =>
      simp only [encode_cons]
      cases i with
      | zero =>
          simpa using List.getElem_append_left (as := (c a).val) (bs := encode c x)
            (i := r) (by rw [(c a).property]; exact hr)
      | succ i =>
          rw [List.getElem_append_right (by rw [(c a).property, Nat.add_mul]; omega)]
          have he : (i + 1) * P + r - (c a).val.length = i * P + r := by
            rw [(c a).property, Nat.add_mul]; omega
          simpa only [he, List.getElem_cons_succ] using ih i (by simpa using hi)

end TreeEdit

end OAI

-- ---- platform node ----
open OAI OAI.TreeEdit


theorem solution.{u} : type_of% @_root_.OAI.TreeEdit.get_encode_block.{u} := @_root_.OAI.TreeEdit.get_encode_block.{u}
