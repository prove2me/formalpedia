-- Prove2me | solution 1 for KernelRank.finiteDimensional_rowSpan_of_isSumOfProducts
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:57:00.279372+00:00
-- url     : https://prove2.me/submissions/c93bed78-0680-4f59-a1d4-c178d224474e

import Definitions.Def_KernelRankLean_Defs
import Definitions.Def_KernelRankLean_RowSpan
import Theorems.Thm_KernelRank_rowSpan_le_of_isSumOfProducts

set_option autoImplicit true
open KernelRank
variable {𝕜 α : Type*}
variable [Field 𝕜]
namespace KernelRank
theorem _root_.solution {K : (Fin 2 → α) → 𝕜} {N : ℕ}
    (hK : IsSumOfProducts K N) : FiniteDimensional 𝕜 (rowSpan K) := by
  obtain ⟨f, hK⟩ := hK
  have := FiniteDimensional.span_of_finite 𝕜 (Set.finite_range fun n => f n 0)
  exact Submodule.finiteDimensional_of_le (rowSpan_le_of_isSumOfProducts hK)
end KernelRank
