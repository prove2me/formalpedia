-- Prove2me | solution 1 for KernelRank.separableRank_padTwo_le_of_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:43:46.055401+00:00
-- url     : https://prove2.me/submissions/fb1a485f-3548-4d64-8c1a-3dd14c64ef0c

import Definitions.Def_KernelRankLean_Main
import Definitions.Def_KernelRankLean_Approximation
import Theorems.Thm_KernelRank_separableRank_fin2_le_of_tendsto
import Theorems.Thm_KernelRank_separableRank_padTwo_le


set_option autoImplicit true
open Complex Polynomial
open scoped Topology
open KernelRank
namespace KernelRank
theorem _root_.solution {𝕜 α ι : Type*} [Field 𝕜] [TopologicalSpace 𝕜]
    [IsTopologicalRing 𝕜] [T2Space 𝕜] [Zero α] {d : ℕ} (hd : 2 ≤ d)
    {l : Filter ι} [l.NeBot] {F : ι → (Fin d → α) → 𝕜} {K : (Fin d → α) → 𝕜} {r : ℕ}
    (hrank : ∀ᶠ i in l, separableRank (F i) ≤ (r : ℕ))
    (htend : ∀ x, Filter.Tendsto (fun i => F i x) l (𝓝 (K x))) :
    separableRank (fun y : Fin 2 → α => K (padTwo y)) ≤ (r : ℕ) := by
  refine separableRank_fin2_le_of_tendsto (F := fun i y => F i (padTwo y)) ?_
    (fun y => htend (padTwo y))
  filter_upwards [hrank] with i hi
  exact (separableRank_padTwo_le hd (F i)).trans hi
end KernelRank
