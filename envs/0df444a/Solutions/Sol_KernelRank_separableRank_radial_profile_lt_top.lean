-- Prove2me | solution 1 for KernelRank.separableRank_radial_profile_lt_top
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:45:44.944794+00:00
-- url     : https://prove2.me/submissions/323c3d07-6b47-4ab3-a40e-aba1a73371a2

import Definitions.Def_KernelRankLean_MultiComplexRank
import Definitions.Def_KernelRankLean_RealExpPoly
import Definitions.Def_KernelRankLean_MultiRealRank
import Theorems.Thm_KernelRank_isSumOfProducts_radial_component
import Theorems.Thm_KernelRank_IsSumOfProducts_comp
import Theorems.Thm_KernelRank_IsSumOfProducts_finsetSum


set_option autoImplicit true
open Complex Polynomial NNReal
open KernelRank
namespace KernelRank
theorem _root_.solution {d : ℕ} (hd : 2 ≤ d) (cs : List Component) :
    separableRank (fun x : Fin d → ℝ => profile cs (∑ j, x j ^ 2)) < ⊤ := by
  let comp (i : Fin cs.length) : Component := cs[i]
  have hprof : (fun x : Fin d → ℝ => profile cs (∑ j, x j ^ 2)) =
      fun x => ∑ i : Fin cs.length, (comp i).eval (∑ j, x j ^ 2) := by
    funext x
    exact (Fin.sum_univ_fun_getElem cs fun c => c.eval (∑ j, x j ^ 2)).symm
  rw [hprof]
  exact lt_of_le_of_lt
    (iInf₂_le _ (IsSumOfProducts.finsetSum fun i => isSumOfProducts_radial_component hd (comp i)))
    (WithTop.coe_lt_top _)
end KernelRank
