-- Prove2me | solution 1 for OAI.FiniteCircle.WordMatching.le_lcs
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T14:30:40.468656+00:00
-- url     : https://prove2.me/submissions/7463e09a-1ce8-426e-84a3-ed177fb05ed3

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/FiniteCircle/Matching.lean:L147-L164
-- (upload_full_project.md Phase 4): solution for node OAI.FiniteCircle.WordMatching.le_lcs. The node keeps its source
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

theorem le_lcs (A : WordMatching x y q) : q ≤ lcs x y := by
  let z := List.ofFn (fun i : Fin q => x.get (A.left i))
  have hx : z <+ x := by
    apply List.sublist_iff_exists_fin_orderEmbedding_get_eq.mpr
    have he : z.length = q := List.length_ofFn
    refine ⟨(Fin.castOrderIso he).toOrderEmbedding.trans A.left, ?_⟩
    intro i
    change (List.ofFn (fun j : Fin q => x.get (A.left j))).get i = x.get (A.left (Fin.cast he i))
    rw [List.get_ofFn]
  have hy : z <+ y := by
    apply List.sublist_iff_exists_fin_orderEmbedding_get_eq.mpr
    have he : z.length = q := List.length_ofFn
    refine ⟨(Fin.castOrderIso he).toOrderEmbedding.trans A.right, ?_⟩
    intro i
    change (List.ofFn (fun j : Fin q => x.get (A.left j))).get i = y.get (A.right (Fin.cast he i))
    rw [List.get_ofFn]
    convert A.letters (Fin.cast he i) using 1
  simpa [z] using FiniteCircle.le_lcs hx hy

end WordMatching

namespace WordMatching
variable {α : Type*} {x y : List α} {q : ℕ}

end WordMatching

namespace WordMatching
variable {α : Type*} {x y : List α} {q : ℕ}

end WordMatching

end FiniteCircle

end OAI

-- ---- platform node ----
open OAI OAI.FiniteCircle OAI.FiniteCircle.WordMatching
open scoped BigOperators List


theorem solution : type_of% @_root_.OAI.FiniteCircle.WordMatching.le_lcs := @_root_.OAI.FiniteCircle.WordMatching.le_lcs
