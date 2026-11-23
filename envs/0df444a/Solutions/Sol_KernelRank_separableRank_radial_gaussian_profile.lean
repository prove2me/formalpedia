-- Prove2me | solution 1 for KernelRank.separableRank_radial_gaussian_profile
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:51:36.786871+00:00
-- url     : https://prove2.me/submissions/35510860-98da-429d-8b1c-d273269ac9a6

import Definitions.Def_KernelRankLean_MultiComplexRank
import Definitions.Def_KernelRankLean_RealExpPoly
import Definitions.Def_KernelRankLean_MultiRealRank
import Theorems.Thm_KernelRank_separableRank_radial_profile
import Theorems.Thm_KernelRank_multiTotalCost_of_isGaussian


set_option autoImplicit true
open Complex Polynomial NNReal
open KernelRank
namespace KernelRank
theorem _root_.solution {d : ℕ} (hd : 2 ≤ d) {cs : List Component}
    (hcs : IsGaussianRepresentation cs) :
    separableRank (fun x : Fin d → ℝ => profile cs (∑ j, x j ^ 2)) =
      gaussianTotalCost d cs := by
  rw [separableRank_radial_profile hd hcs.1, multiTotalCost_of_isGaussian hcs.2]
end KernelRank
