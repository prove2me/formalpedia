-- Prove2me | solution 1 for KernelRank.isSumOfProducts_radial_component
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:43:33.700998+00:00
-- url     : https://prove2.me/submissions/f61dab3b-cd85-47e5-b122-a2a8e094336f

import Definitions.Def_KernelRankLean_MultiComplexRank
import Definitions.Def_KernelRankLean_RealExpPoly
import Definitions.Def_KernelRankLean_MultiRealRank
import Theorems.Thm_KernelRank_IsSumOfProducts_comp
import Theorems.Thm_KernelRank_isSumOfProducts_expPoly


set_option autoImplicit true
open Complex Polynomial NNReal
open KernelRank
namespace KernelRank
theorem _root_.solution {d : ℕ} (hd : 2 ≤ d) (c : Component) :
    IsSumOfProducts (fun x : Fin d → ℝ => c.eval (∑ j, x j ^ 2))
      (((d - 1) * c.poly.natDegree + 1) * d) := by
  have hcpx : IsSumOfProducts
      (fun x : Fin d → ℝ => expPoly c.poly c.rate (∑ j, x j ^ 2))
      ((d - 1) * c.poly.natDegree + 1) :=
    (isSumOfProducts_expPoly hd c.poly c.rate).comp
      (fun _ x => (⟨x ^ 2, sq_nonneg x⟩ : ℝ≥0))
  exact hcpx.re (by omega)
end KernelRank
