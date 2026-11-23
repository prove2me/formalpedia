-- Prove2me | solution 1 for KernelRank.separableRank_lt_top_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:25:08.070259+00:00
-- url     : https://prove2.me/submissions/28a2b2c7-7d59-4d42-9cc8-914c14d517ce

import Definitions.Def_KernelRankLean_Defs
import Definitions.Def_KernelRankLean_RowSpan
import Theorems.Thm_KernelRank_fin2Vec_zero
import Theorems.Thm_KernelRank_fin2Vec_one
import Theorems.Thm_KernelRank_finiteDimensional_rowSpan_of_isSumOfProducts
import Theorems.Thm_KernelRank_isSumOfProducts_finrank_rowSpan
attribute [local simp] KernelRank.fin2Vec_zero
attribute [local simp] KernelRank.fin2Vec_one

set_option autoImplicit true
open KernelRank
variable {𝕜 α : Type*}
variable [Field 𝕜]
namespace KernelRank
theorem _root_.solution (K : (Fin 2 → α) → 𝕜) :
    separableRank K < ⊤ ↔ FiniteDimensional 𝕜 (rowSpan K) := by
  constructor
  · intro hlt
    by_contra hfin
    refine hlt.ne (iInf₂_eq_top.mpr fun N hN => ?_)
    exact absurd (finiteDimensional_rowSpan_of_isSumOfProducts hN) hfin
  · intro hfin
    exact lt_of_le_of_lt (iInf₂_le _ (isSumOfProducts_finrank_rowSpan K)) (by simp)
end KernelRank
