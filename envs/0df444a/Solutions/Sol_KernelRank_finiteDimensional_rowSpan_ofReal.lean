-- Prove2me | solution 1 for KernelRank.finiteDimensional_rowSpan_ofReal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:55:29.417605+00:00
-- url     : https://prove2.me/submissions/eb6cf268-ad0d-4522-b6ec-9f79a6305ad6

import Definitions.Def_KernelRankLean_RowSpan
import Definitions.Def_KernelRankLean_Complexification
import Theorems.Thm_KernelRank_fin2Vec_one
import Theorems.Thm_KernelRank_fin2Vec_zero
import Theorems.Thm_KernelRank_row_mem_rowSpan
attribute [local simp] KernelRank.fin2Vec_one
attribute [local simp] KernelRank.fin2Vec_zero



set_option autoImplicit true
open KernelRank
variable {α : Type*}
namespace KernelRank
theorem _root_.solution (K : (Fin 2 → α) → ℝ)
    [FiniteDimensional ℂ (rowSpan (fun z => (K z : ℂ)))] :
    FiniteDimensional ℝ (rowSpan K) := by
  let re : rowSpan (fun z => (K z : ℂ)) →ₗ[ℝ] (α → ℝ) :=
    { toFun := fun f x => (f.1 x).re
      map_add' := by intros; ext; simp
      map_smul' := by intros; ext; simp }
  have hle : rowSpan K ≤ LinearMap.range re := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨y, rfl⟩
    exact ⟨⟨_, row_mem_rowSpan _ y⟩, by ext x; simp [re]⟩
  exact Submodule.finiteDimensional_of_le hle
end KernelRank
