-- Prove2me | solution 1 for KernelRank.span_range_eq_top_of_dual
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:12:42.791412+00:00
-- url     : https://prove2.me/submissions/31355966-418c-41d1-b82b-bbcbbe3db820

import Definitions.Def_KernelRankLean_ComplexRank
import Definitions.Def_KernelRankLean_MultiComplexRank

set_option autoImplicit true
open Complex Polynomial NNReal
open KernelRank
namespace KernelRank
theorem _root_.solution {𝕜 α V : Type*} [Field 𝕜] [AddCommGroup V] [Module 𝕜 V]
    {v : α → V} (h : ∀ L : V →ₗ[𝕜] 𝕜, (∀ s, L (v s) = 0) → L = 0) :
    Submodule.span 𝕜 (Set.range v) = ⊤ := by
  by_contra hlt
  obtain ⟨L, hLne, hLmap⟩ :=
    Submodule.exists_dual_map_eq_bot_of_lt_top (lt_top_iff_ne_top.mpr hlt) inferInstance
  refine hLne (h L fun s => ?_)
  have hmem : L (v s) ∈ Submodule.map L (Submodule.span 𝕜 (Set.range v)) :=
    ⟨v s, Submodule.subset_span ⟨s, rfl⟩, rfl⟩
  rwa [hLmap, Submodule.mem_bot] at hmem
end KernelRank
