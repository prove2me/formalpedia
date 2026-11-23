-- Prove2me | solution 1 for KernelRank.separableRank_eq_finrank_rowSpan
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:00:38.770614+00:00
-- url     : https://prove2.me/submissions/ae19c3c6-51b6-429e-bdc2-470d352fe853

import Definitions.Def_KernelRankLean_Defs
import Definitions.Def_KernelRankLean_RowSpan
import Theorems.Thm_KernelRank_finrank_rowSpan_le_of_isSumOfProducts
import Theorems.Thm_KernelRank_isSumOfProducts_finrank_rowSpan

set_option autoImplicit true
open KernelRank
variable {𝕜 α : Type*}
variable [Field 𝕜]
namespace KernelRank
theorem _root_.solution (K : (Fin 2 → α) → 𝕜)
    [FiniteDimensional 𝕜 (rowSpan K)] :
    separableRank K = Module.finrank 𝕜 (rowSpan K) := by
  refine le_antisymm (iInf₂_le _ (isSumOfProducts_finrank_rowSpan K)) ?_
  exact le_iInf₂ fun N hN => by exact_mod_cast finrank_rowSpan_le_of_isSumOfProducts hN
end KernelRank
