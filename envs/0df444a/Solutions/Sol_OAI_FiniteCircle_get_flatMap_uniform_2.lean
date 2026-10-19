-- Prove2me | solution 2 for OAI.FiniteCircle.get_flatMap_uniform
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T17:29:22.0781+00:00
-- url     : https://prove2.me/submissions/621362de-f0a9-476f-97b5-f040d0535b4f

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/FiniteCircle/TaggedRows.lean:L324-L352
-- (upload_full_project.md Phase 4): solution for node OAI.FiniteCircle.get_flatMap_uniform. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_FiniteCircle
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Model
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Edit
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Matching
import Definitions.Def_OAI_Combinatorics_FiniteCircle_TaggedRows
import Theorems.Thm_OAI_FiniteCircle_segment_flatMap_uniform

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

theorem get_flatMap_uniform {α β : Type*} (xs : List α) (f : α → List β) {L : ℕ}
    (hL : 0 < L) (hl : ∀ a ∈ xs, (f a).length = L)
    (k : Fin (xs.flatMap f).length) :
    ∃ (i : Fin xs.length) (b : Fin (f (xs.get i)).length),
      i.val = k.val/L ∧ b.val = k.val%L ∧ (xs.flatMap f).get k = (f (xs.get i)).get b := by
  have hk : k.val < xs.length*L := by simpa only [length_flatMap_uniform xs f L hl] using k.isLt
  let i : Fin xs.length := ⟨k.val/L, (Nat.div_lt_iff_lt_mul hL).mpr hk⟩
  have hi := hl (xs.get i) (xs.get_mem i)
  let b : Fin (f (xs.get i)).length := ⟨k.val%L, by rw [hi]; exact Nat.mod_lt _ hL⟩
  refine ⟨i, b, rfl, rfl, ?_⟩
  have hs : i.val*L+L ≤ (xs.flatMap f).length := by
    rw [length_flatMap_uniform xs f L hl]
    have h := Nat.mul_le_mul_right L i.isLt
    nlinarith
  have he := segment_flatMap_uniform xs f L hl i
  let b' : Fin (segment (xs.flatMap f) (i.val*L) L).length :=
    ⟨b.val, by rw [he]; exact b.isLt⟩
  have hg := get_segment (xs.flatMap f) hs b'
  have hpos : i.val*L+b'.val = k.val := by
    change k.val/L*L+k.val%L = k.val
    simpa only [Nat.mul_comm] using Nat.div_add_mod k.val L
  have hg' : (segment (xs.flatMap f) (i.val*L) L).get b' = (xs.flatMap f).get k := by
    convert hg using 1
    congr 1
    exact Fin.ext hpos.symm
  rw [← hg']
  simp only [List.get_eq_getElem]
  simp only [he]
  rfl

end FiniteCircle

end OAI

-- ---- platform node ----
open OAI OAI.FiniteCircle
open scoped BigOperators List


theorem solution : type_of% @_root_.OAI.FiniteCircle.get_flatMap_uniform := @_root_.OAI.FiniteCircle.get_flatMap_uniform
