-- Prove2me | solution 1 for OAI.FiniteCircle.nodup_maskTags
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T14:39:19.364304+00:00
-- url     : https://prove2.me/submissions/2d406ec2-524a-46c8-946b-d84d55fd8325

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/FiniteCircle/CircleWords.lean:L23-L45
-- (upload_full_project.md Phase 4): solution for node OAI.FiniteCircle.nodup_maskTags. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_FiniteCircle
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Model
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Edit
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Matching
import Definitions.Def_OAI_Combinatorics_FiniteCircle_TaggedRows
import Definitions.Def_OAI_Combinatorics_FiniteCircle_PhaseCost
import Definitions.Def_OAI_Combinatorics_FiniteCircle_CircleWords

-- ---- from OAI.Combinatorics.FiniteCircle.CircleWords ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace FiniteCircle

open scoped BigOperators List

theorem nodup_maskTags (h : ℕ) (p : ℕ → ℕ → ℕ) (l : ℕ) :
    (maskTags h p l).Nodup := by
  classical
  unfold maskTags
  have he : (List.ofFn (fun k : Fin h => List.ofFn (fun b : Fin (p l k) => (Sigma.mk k b : MaskTag h p l)))) =
      (List.ofFn (fun k : Fin h => k)).map (fun k : Fin h => List.ofFn (fun b : Fin (p l k) => (Sigma.mk k b : MaskTag h p l))) := by simp only [List.map_ofFn]; rfl
  rw [he, ← List.flatMap_def]
  change ((List.ofFn (fun k : Fin h => k)).flatMap
    (fun k : Fin h => List.ofFn (fun b : Fin (p l k) => (Sigma.mk k b : MaskTag h p l)))).Nodup
  apply List.nodup_flatMap.mpr
  constructor
  · intro k _
    apply List.nodup_ofFn.mpr
    intro a b hab
    simpa only [Sigma.mk.inj_iff, heq_eq_eq, true_and] using hab
  · apply List.pairwise_ofFn.mpr
    intro i j hij
    apply List.disjoint_left.mpr
    intro a ha hb
    obtain ⟨u,hu⟩ := List.mem_ofFn.mp ha
    obtain ⟨v,hv⟩ := List.mem_ofFn.mp hb
    have he : i = j := congrArg Sigma.fst (hu.trans hv.symm)
    exact (Fin.ne_of_lt hij) he

namespace PhaseCost
variable {G : Type*} [AddCommGroup G]

end PhaseCost

end FiniteCircle

end OAI

-- ---- platform node ----
open OAI OAI.FiniteCircle
open scoped BigOperators List


theorem solution : type_of% @_root_.OAI.FiniteCircle.nodup_maskTags := @_root_.OAI.FiniteCircle.nodup_maskTags
