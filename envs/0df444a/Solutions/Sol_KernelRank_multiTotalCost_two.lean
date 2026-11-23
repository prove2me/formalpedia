-- Prove2me | solution 1 for KernelRank.multiTotalCost_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:27:13.087588+00:00
-- url     : https://prove2.me/submissions/31f451ef-8e64-4ab6-b16f-507c1f87000b

import Mathlib
import Definitions.Def_KernelRankLean_Defs
import Theorems.Thm_KernelRank_Component_multiCost_two

set_option autoImplicit true
open Complex Polynomial
open KernelRank
namespace KernelRank
theorem _root_.solution (cs : List Component) : multiTotalCost 2 cs = totalCost cs := by
  unfold multiTotalCost totalCost
  congr 1
  exact List.map_congr_left fun c _ => c.multiCost_two
end KernelRank
