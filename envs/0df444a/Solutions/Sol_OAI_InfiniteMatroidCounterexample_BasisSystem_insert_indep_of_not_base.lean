-- Prove2me | solution 1 for OAI.InfiniteMatroidCounterexample.BasisSystem.insert_indep_of_not_base
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T06:05:38.65498+00:00
-- url     : https://prove2.me/submissions/6520a6bd-acc1-4f1d-8866-fb682e5bbbee

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/InfiniteMatroid/Matroid.lean:L97-L111
-- (upload_full_project.md Phase 4): solution for node OAI.InfiniteMatroidCounterexample.BasisSystem.insert_indep_of_not_base. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_InfiniteMatroidCorollaries
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_Matroid__InfiniteMatroidCorollaries

-- ---- from OAI.Combinatorics.InfiniteMatroid.Matroid ----
namespace OAI

section

open Set Matroid

namespace InfiniteMatroidCounterexample

namespace BasisSystem

variable {α : Type*} (S : BasisSystem α)

lemma insert_indep_of_not_base {I : Set α} (hI : S.matroid.Indep I)
    (hnot : ¬ S.matroid.IsBase I) (e : α) : S.matroid.Indep (insert e I) := by
  obtain ⟨B, hB, hIB⟩ := hI
  by_cases heB : e ∈ B
  · exact ⟨B, hB, Set.insert_subset heB hIB⟩
  have hn : ¬ B ⊆ I := by
    intro hBI
    exact hnot ((Subset.antisymm hIB hBI) ▸ hB)
  obtain ⟨f, hfB, hfI⟩ := Set.not_subset.mp hn
  refine ⟨insert e (B \ {f}), S.swap hB f hfB e heB, ?_⟩
  intro x hx
  rcases hx with rfl | hx
  · exact Set.mem_insert _ _
  · right
    exact ⟨hIB hx, fun hxf ↦ hfI (Set.mem_singleton_iff.mp hxf ▸ hx)⟩

end BasisSystem
end InfiniteMatroidCounterexample
end

end OAI

-- ---- platform node ----
open OAI OAI.InfiniteMatroidCounterexample OAI.InfiniteMatroidCounterexample.BasisSystem
open Set Matroid


theorem solution : type_of% @_root_.OAI.InfiniteMatroidCounterexample.BasisSystem.insert_indep_of_not_base := @_root_.OAI.InfiniteMatroidCounterexample.BasisSystem.insert_indep_of_not_base
