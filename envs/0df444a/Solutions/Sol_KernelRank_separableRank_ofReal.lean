-- Prove2me | solution 1 for KernelRank.separableRank_ofReal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:45:00.136808+00:00
-- url     : https://prove2.me/submissions/9ecb7e4a-442d-4a90-a7b0-c078ed4a5143

import Definitions.Def_KernelRankLean_RowSpan
import Definitions.Def_KernelRankLean_Complexification
import Theorems.Thm_KernelRank_separableRank_ofReal_le
import Theorems.Thm_KernelRank_finiteDimensional_rowSpan_ofReal
import Theorems.Thm_KernelRank_finrank_rowSpan_ofReal
import Theorems.Thm_KernelRank_finiteDimensional_rowSpan_of_isSumOfProducts
import Theorems.Thm_KernelRank_finrank_rowSpan_le_of_isSumOfProducts
import Theorems.Thm_KernelRank_separableRank_eq_finrank_rowSpan


set_option autoImplicit true
open KernelRank
variable {α : Type*}
namespace KernelRank
theorem _root_.solution (K : (Fin 2 → α) → ℝ) :
    separableRank (fun z => (K z : ℂ)) = separableRank K := by
  refine le_antisymm (separableRank_ofReal_le K) ?_
  refine le_iInf₂ fun N hN => ?_
  let := finiteDimensional_rowSpan_of_isSumOfProducts hN
  let := finiteDimensional_rowSpan_ofReal K
  rw [separableRank_eq_finrank_rowSpan, finrank_rowSpan_ofReal]
  exact_mod_cast finrank_rowSpan_le_of_isSumOfProducts hN
end KernelRank
