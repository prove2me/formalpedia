-- Prove2me | solution 1 for KernelRank.multiTotalCost_of_isGaussian
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:27:14.919613+00:00
-- url     : https://prove2.me/submissions/b2a6c4b5-b287-49c6-896a-3ed4320cbb42

import Mathlib
import Definitions.Def_KernelRankLean_Defs
import Theorems.Thm_KernelRank_Component_multiCost_of_isGaussian

set_option autoImplicit true
open Complex Polynomial
open KernelRank
namespace KernelRank
theorem _root_.solution {d : ℕ} {cs : List Component}
    (hg : ∀ c ∈ cs, c.IsGaussian) :
    multiTotalCost d cs = gaussianTotalCost d cs := by
  unfold multiTotalCost gaussianTotalCost
  congr 1
  exact List.map_congr_left fun c hc => Component.multiCost_of_isGaussian d (hg c hc)
end KernelRank
