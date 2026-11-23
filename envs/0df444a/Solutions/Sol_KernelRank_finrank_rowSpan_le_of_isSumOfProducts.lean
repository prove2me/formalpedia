-- Prove2me | solution 1 for KernelRank.finrank_rowSpan_le_of_isSumOfProducts
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:57:07.838773+00:00
-- url     : https://prove2.me/submissions/94a265f8-6839-4f2c-85da-7ebd33a9fddf

import Definitions.Def_KernelRankLean_Defs
import Definitions.Def_KernelRankLean_RowSpan
import Theorems.Thm_KernelRank_rowSpan_le_of_isSumOfProducts

set_option autoImplicit true
open KernelRank
variable {𝕜 α : Type*}
variable [Field 𝕜]
namespace KernelRank
theorem _root_.solution {K : (Fin 2 → α) → 𝕜} {N : ℕ}
    (hK : IsSumOfProducts K N) : Module.finrank 𝕜 (rowSpan K) ≤ N := by
  obtain ⟨f, hK⟩ := hK
  have := FiniteDimensional.span_of_finite 𝕜 (Set.finite_range fun n => f n 0)
  calc Module.finrank 𝕜 (rowSpan K)
      ≤ Module.finrank 𝕜 (Submodule.span 𝕜 (Set.range fun n => f n 0)) :=
        Submodule.finrank_mono (rowSpan_le_of_isSumOfProducts hK)
    _ ≤ Fintype.card (Fin N) := finrank_range_le_card fun n => f n 0
    _ = N := Fintype.card_fin N
end KernelRank
