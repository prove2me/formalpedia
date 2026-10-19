-- Prove2me | solution 1 for OAI.FiniteCircle.segment_flatMap_uniform
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T17:26:35.161357+00:00
-- url     : https://prove2.me/submissions/c502f845-11ec-484c-8165-634cc03f5346

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/FiniteCircle/TaggedRows.lean:L308-L322
-- (upload_full_project.md Phase 4): solution for node OAI.FiniteCircle.segment_flatMap_uniform. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_FiniteCircle
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Model
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Edit
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Matching
import Definitions.Def_OAI_Combinatorics_FiniteCircle_TaggedRows

-- ---- from OAI.Combinatorics.FiniteCircle.TaggedRows ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace FiniteCircle

open scoped BigOperators List

namespace WordMatching
variable {β : Type*} {x y : List β} {q : ℕ}

end WordMatching

namespace WordMatching
variable {β : Type*} {x y : List β} {q : ℕ}

end WordMatching

theorem segment_flatMap_uniform {α β : Type*} (xs : List α) (f : α → List β) (L : ℕ)
    (hl : ∀ a ∈ xs, (f a).length = L) (i : Fin xs.length) :
    segment (xs.flatMap f) (i.val*L) L = f (xs.get i) := by
  have he : xs = xs.take i.val ++ xs[i.val] :: xs.drop (i.val+1) := by
    conv_lhs => rw [← List.take_append_drop i.val xs, List.drop_eq_getElem_cons i.isLt]
  have hp : ((xs.take i.val).flatMap f).length = i.val*L := by
    rw [length_flatMap_uniform _ f L (fun a ha => hl a (List.mem_of_mem_take ha)),
      List.length_take_of_le i.isLt.le]
  have hi := hl (xs.get i) (xs.get_mem i)
  have hf := congrArg (fun ys => ys.flatMap f) he
  rw [List.flatMap_append, List.flatMap_cons] at hf
  rw [hf]
  unfold segment
  rw [← hp, List.drop_left, List.take_append_of_le_length (by simpa only [List.get_eq_getElem] using hi.ge)]
  simpa only [List.get_eq_getElem] using List.take_of_length_le (by simpa only [List.get_eq_getElem] using hi.le)

end FiniteCircle

end OAI

-- ---- platform node ----
open OAI OAI.FiniteCircle
open scoped BigOperators List


theorem solution : type_of% @_root_.OAI.FiniteCircle.segment_flatMap_uniform := @_root_.OAI.FiniteCircle.segment_flatMap_uniform
