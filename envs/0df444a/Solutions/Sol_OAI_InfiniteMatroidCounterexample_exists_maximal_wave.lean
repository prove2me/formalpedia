-- Prove2me | solution 1 for OAI.InfiniteMatroidCounterexample.exists_maximal_wave
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T06:08:46.483406+00:00
-- url     : https://prove2.me/submissions/7e2c405d-0933-49ba-ab20-51400d9cffe9

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/InfiniteMatroid/Waves.lean:L14-L44
-- (upload_full_project.md Phase 4): solution for node OAI.InfiniteMatroidCounterexample.exists_maximal_wave. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_InfiniteMatroidCorollaries
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_Matroid__InfiniteMatroidCorollaries
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_DoubleRay__InfiniteMatroidCorollaries
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_Waves

-- ---- from OAI.Combinatorics.InfiniteMatroid.Waves ----
namespace OAI

namespace InfiniteMatroidCounterexample
open Set Matroid

theorem exists_maximal_wave {α ι : Type*} (M : ι → Matroid α) (F : Set α) :
    ∃ W, Maximal (Wave M F) W := by
  classical
  apply zorn_le₀ {W | Wave M F W}
  intro c hc hchain
  let U : Set α × (ι → Set α) :=
    (⋃ W : c, W.1.1, fun i ↦ ⋃ W : c, W.1.2 i)
  have hle : ∀ W ∈ c, W ≤ U := by
    intro W hW
    refine ⟨?_, fun i ↦ ?_⟩
    · exact subset_iUnion_of_subset ⟨W, hW⟩ Subset.rfl
    · exact subset_iUnion_of_subset ⟨W, hW⟩ Subset.rfl
  refine ⟨U, ?_, hle⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨W, hx⟩ := mem_iUnion.mp hx
    exact (hc W.2).1 hx
  · intro i x hx
    obtain ⟨W, hx⟩ := mem_iUnion.mp hx
    exact (hle W W.2).1 ((hc W.2).2.1 i hx)
  · intro i j hij
    apply disjoint_left.mpr
    intro x hxi hxj
    obtain ⟨W, hxW⟩ := mem_iUnion.mp hxi
    obtain ⟨V, hxV⟩ := mem_iUnion.mp hxj
    rcases hchain.total W.2 V.2 with hWV | hVW
    · exact disjoint_left.mp ((hc V.2).2.2.1 hij) (hWV.2 i hxW) hxV
    · exact disjoint_left.mp ((hc W.2).2.2.1 hij) hxW (hVW.2 j hxV)
  · intro i x hx
    obtain ⟨W, hx⟩ := mem_iUnion.mp hx
    exact (M i).closure_mono ((hle W W.2).2 i) ((hc W.2).2.2.2 i hx)

end InfiniteMatroidCounterexample

end OAI

-- ---- platform node ----
open OAI OAI.InfiniteMatroidCounterexample
open Set Matroid


theorem solution : type_of% @_root_.OAI.InfiniteMatroidCounterexample.exists_maximal_wave := @_root_.OAI.InfiniteMatroidCounterexample.exists_maximal_wave
