-- Prove2me | solution 1 for KernelRank.radial_congr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:16:03.419981+00:00
-- url     : https://prove2.me/submissions/5a4cedff-987b-4e3a-a359-e133b79f28a3

import Definitions.Def_KernelRankLean_Necessity
import Definitions.Def_KernelRankLean_MultiComplexRank
import Definitions.Def_KernelRankLean_MultiRealRank
import Definitions.Def_KernelRankLean_Main

set_option autoImplicit true
open Complex Polynomial Filter Topology
open KernelRank
namespace KernelRank
theorem _root_.solution {d : ℕ} {𝕜 : Type*} {φ ψ : ℝ → 𝕜} (h : ∀ s, 0 ≤ s → φ s = ψ s) :
    (fun x : Fin d → ℝ => φ (∑ j, x j ^ 2)) = fun x => ψ (∑ j, x j ^ 2) :=
  funext fun x => h _ (Finset.sum_nonneg fun j _ => sq_nonneg (x j))
end KernelRank
