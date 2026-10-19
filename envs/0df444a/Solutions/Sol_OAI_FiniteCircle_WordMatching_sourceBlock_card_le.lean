-- Prove2me | solution 1 for OAI.FiniteCircle.WordMatching.sourceBlock_card_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T14:32:03.410698+00:00
-- url     : https://prove2.me/submissions/cf98f7f5-265d-4bff-a03b-06d4dd3190c6

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/FiniteCircle/Matching.lean:L230-L246
-- (upload_full_project.md Phase 4): solution for node OAI.FiniteCircle.WordMatching.sourceBlock_card_le. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_FiniteCircle
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Model
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Edit
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Matching

-- ---- from OAI.Combinatorics.FiniteCircle.Matching ----
namespace OAI

namespace FiniteCircle

open scoped BigOperators List

namespace Slide
variable {α : Type*} {x y : List α}

end Slide

namespace SlidePath
variable {α : Type*} {x y z : List α} {n m : ℕ}

end SlidePath

namespace WordMatching
variable {α : Type*} {x y : List α} {q : ℕ}

end WordMatching

namespace WordMatching
variable {α : Type*} {x y : List α} {q : ℕ}

theorem sourceBlock_card_le (A : WordMatching x y q) {w : ℕ} (hw : 0 < w) (i : ℕ) :
    (A.sourceBlock w i).card ≤ w := by
  let f : Fin q → Fin w := fun k => ⟨(A.left k).val % w, Nat.mod_lt _ hw⟩
  have h : Set.InjOn f (↑(A.sourceBlock w i) : Set (Fin q)) := by
    intro j hj k hk he
    apply A.left.injective
    apply Fin.ext
    have hj := (A.mem_sourceBlock w i j).mp hj
    have hk := (A.mem_sourceBlock w i k).mp hk
    have hf : (A.left j).val % w = (A.left k).val % w := congrArg Fin.val he
    have h1 := Nat.mod_add_div (A.left j).val w
    have h2 := Nat.mod_add_div (A.left k).val w
    rw [hj, hf] at h1
    rw [hk] at h2
    omega
  have hc := Finset.card_le_card_of_injOn f (fun _ _ => Finset.mem_univ _) h
  simpa using hc

end WordMatching

namespace WordMatching
variable {α : Type*} {x y : List α} {q : ℕ}

end WordMatching

end FiniteCircle

end OAI

-- ---- platform node ----
open OAI OAI.FiniteCircle OAI.FiniteCircle.WordMatching
open scoped BigOperators List


theorem solution : type_of% @_root_.OAI.FiniteCircle.WordMatching.sourceBlock_card_le := @_root_.OAI.FiniteCircle.WordMatching.sourceBlock_card_le
