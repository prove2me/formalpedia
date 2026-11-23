-- Prove2me | solution 1 for KernelRank.isSumOfProducts_finrank_rowSpan
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:57:54.234939+00:00
-- url     : https://prove2.me/submissions/06b93abe-b28c-4cc2-8048-fe502ede089b

import Definitions.Def_KernelRankLean_Defs
import Definitions.Def_KernelRankLean_RowSpan
import Theorems.Thm_KernelRank_fin2Vec_zero
import Theorems.Thm_KernelRank_fin2Vec_one
import Theorems.Thm_KernelRank_fin2Vec_eta
import Theorems.Thm_KernelRank_row_mem_rowSpan
attribute [local simp] KernelRank.fin2Vec_zero
attribute [local simp] KernelRank.fin2Vec_one

set_option autoImplicit true
open KernelRank
variable {𝕜 α : Type*}
variable [Field 𝕜]
namespace KernelRank
theorem _root_.solution (K : (Fin 2 → α) → 𝕜)
    [FiniteDimensional 𝕜 (rowSpan K)] :
    IsSumOfProducts K (Module.finrank 𝕜 (rowSpan K)) := by
  let b := Module.finBasis 𝕜 (rowSpan K)
  refine ⟨fun i => fin2Vec (b i : α → 𝕜) (fun y => b.repr ⟨_, row_mem_rowSpan K y⟩ i), fun z => ?_⟩
  have := congrArg (fun w : rowSpan K => (w : α → 𝕜) (z 0))
    (b.sum_repr ⟨_, row_mem_rowSpan K (z 1)⟩)
  simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul] at this
  conv_lhs => rw [← fin2Vec_eta z]
  rw [← this]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fin.prod_univ_two]
  exact mul_comm _ _
end KernelRank
