-- Prove2me | solution 1 for OAI.TreeEdit.segment_encode_block
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T02:36:45.414974+00:00
-- url     : https://prove2.me/submissions/a78854a0-54cd-4642-8b30-1cd66c7c3ece

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/TreeEdit/SegmentComparison.lean:L69-L83
-- (upload_full_project.md Phase 4): solution for node OAI.TreeEdit.segment_encode_block. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_TreeEdit
import Definitions.Def_OAI_Combinatorics_TreeEdit_Model
import Definitions.Def_OAI_Combinatorics_TreeEdit_FiniteProbability
import Definitions.Def_OAI_Combinatorics_TreeEdit_EditMetric
import Definitions.Def_OAI_Combinatorics_TreeEdit_Alignments
import Definitions.Def_OAI_Combinatorics_TreeEdit_SegmentComparison
import Theorems.Thm_OAI_TreeEdit_get_encode_block

-- ---- from OAI.Combinatorics.TreeEdit.SegmentComparison ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace TreeEdit

universe u

variable {α : Type u} {x y z : List α}

theorem length_segment {β : Type*} (x : List β) {start len : ℕ}
    (h : start + len ≤ x.length) : (segment x start len).length = len := by
  simp only [segment, List.length_take, List.length_drop]
  omega

theorem segment_get {β : Type*} (x : List β) (start len i : ℕ)
    (hi : i < (segment x start len).length) :
    (segment x start len)[i] = x[start + i]'(by
      simp only [segment, List.length_take, List.length_drop] at hi
      omega) := by
  simp only [segment, List.getElem_take, List.getElem_drop]

theorem segment_encode_block {P : ℕ} (c : α → Word Bool P) (x : List α)
    (i start len : ℕ) (hi : i < x.length) (hseg : start + len ≤ P) :
    segment (encode c x) (i * P + start) len = segment (c x[i]).val start len := by
  have hb : i * P + start + len ≤ (encode c x).length := by
    rw [length_encode]
    have hh := Nat.mul_le_mul_right P (Nat.succ_le_of_lt hi)
    rw [Nat.succ_mul] at hh
    omega
  have hc : start + len ≤ (c x[i]).val.length := by rwa [(c x[i]).property]
  apply List.ext_getElem
  · rw [length_segment _ hb, length_segment _ hc]
  · intro j hj hj'
    rw [segment_get, segment_get]
    have hjl : j < len := by rwa [length_segment _ hb] at hj
    simpa only [Nat.add_assoc] using get_encode_block c x i (start + j) hi (by omega)

end TreeEdit

end OAI

-- ---- platform node ----
open OAI OAI.TreeEdit


theorem solution.{u} : type_of% @_root_.OAI.TreeEdit.segment_encode_block.{u} := @_root_.OAI.TreeEdit.segment_encode_block.{u}
