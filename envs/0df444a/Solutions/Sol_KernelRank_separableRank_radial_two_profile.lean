-- Prove2me | solution 1 for KernelRank.separableRank_radial_two_profile
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:51:37.298726+00:00
-- url     : https://prove2.me/submissions/20f285f4-acd6-4cac-9d0c-3de52e89fbe7

import Definitions.Def_KernelRankLean_MultiComplexRank
import Definitions.Def_KernelRankLean_RealExpPoly
import Definitions.Def_KernelRankLean_MultiRealRank
import Theorems.Thm_KernelRank_separableRank_radial_profile
import Theorems.Thm_KernelRank_multiTotalCost_two


set_option autoImplicit true
open Complex Polynomial NNReal
open KernelRank
namespace KernelRank
theorem _root_.solution {cs : List Component} (hcs : IsRepresentation cs) :
    separableRank (fun x : Fin 2 → ℝ => profile cs (∑ j, x j ^ 2)) = totalCost cs := by
  rw [separableRank_radial_profile (le_refl 2) hcs, multiTotalCost_two]
end KernelRank
