-- Prove2me | solution 1 for KernelRank.IsSumOfProducts.ofReal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:51:52.675772+00:00
-- url     : https://prove2.me/submissions/3589ef0f-7d5a-4978-bf66-394529c45c8b

import Definitions.Def_KernelRankLean_RowSpan
import Definitions.Def_KernelRankLean_Complexification
import Theorems.Thm_KernelRank_fin2Vec_one
import Theorems.Thm_KernelRank_fin2Vec_zero
attribute [local simp] KernelRank.fin2Vec_one
attribute [local simp] KernelRank.fin2Vec_zero



set_option autoImplicit true
open KernelRank
namespace KernelRank
namespace IsSumOfProducts
theorem _root_.solution {ι : Type*} [Fintype ι] {X : ι → Type*} {K : (∀ i, X i) → ℝ}
    {N : ℕ} (hK : IsSumOfProducts K N) :
    IsSumOfProducts (fun x => (K x : ℂ)) N := by
  obtain ⟨f, hK⟩ := hK
  refine ⟨fun n i x => (f n i x : ℂ), fun x => ?_⟩
  simp only [hK, Complex.ofReal_sum, Complex.ofReal_prod]
end IsSumOfProducts
end KernelRank
