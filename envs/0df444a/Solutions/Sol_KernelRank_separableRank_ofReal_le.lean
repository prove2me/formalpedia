-- Prove2me | solution 1 for KernelRank.separableRank_ofReal_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:26:25.556314+00:00
-- url     : https://prove2.me/submissions/60a23e0e-802b-47ff-8f9e-dd4a72bdc457

import Definitions.Def_KernelRankLean_RowSpan
import Definitions.Def_KernelRankLean_Complexification
import Theorems.Thm_KernelRank_IsSumOfProducts_ofReal

set_option autoImplicit true
open KernelRank
namespace KernelRank
theorem _root_.solution {ι : Type*} [Fintype ι] {X : ι → Type*}
    (K : (∀ i, X i) → ℝ) :
    separableRank (fun x => (K x : ℂ)) ≤ separableRank K :=
  le_iInf₂ fun _ hN => iInf₂_le _ hN.ofReal
end KernelRank
