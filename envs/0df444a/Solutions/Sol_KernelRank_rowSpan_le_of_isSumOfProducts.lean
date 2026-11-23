-- Prove2me | solution 1 for KernelRank.rowSpan_le_of_isSumOfProducts
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:54:59.969981+00:00
-- url     : https://prove2.me/submissions/d83a3606-8d18-465f-8894-7c3d3397d305

import Definitions.Def_KernelRankLean_Defs
import Definitions.Def_KernelRankLean_RowSpan
import Theorems.Thm_KernelRank_fin2Vec_zero
import Theorems.Thm_KernelRank_fin2Vec_one
attribute [local simp] KernelRank.fin2Vec_zero
attribute [local simp] KernelRank.fin2Vec_one

set_option autoImplicit true
open KernelRank
variable {𝕜 α : Type*}
variable [Field 𝕜]
namespace KernelRank
theorem _root_.solution {K : (Fin 2 → α) → 𝕜} {N : ℕ}
    {f : Fin N → Fin 2 → α → 𝕜}
    (hK : ∀ z, K z = ∑ n, ∏ i : Fin 2, f n i (z i)) :
    rowSpan K ≤ Submodule.span 𝕜 (Set.range fun n => f n 0) := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨y, rfl⟩
  have : (fun x => K (fin2Vec x y)) = ∑ n, f n 1 y • f n 0 := by
    funext x
    simp [hK, Fin.prod_univ_two, Finset.sum_apply, mul_comm]
  change (fun x => K (fin2Vec x y)) ∈ Submodule.span 𝕜 (Set.range fun n => f n 0)
  rw [this]
  exact Submodule.sum_mem _ fun n _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨n, rfl⟩)
end KernelRank
