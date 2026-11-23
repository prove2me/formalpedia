-- Prove2me | solution 1 for KernelRank.finrank_rowSpan_ofReal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:29:50.549474+00:00
-- url     : https://prove2.me/submissions/e8626ec0-1b25-4566-8f9e-6a578887db0a

import Definitions.Def_KernelRankLean_RowSpan
import Definitions.Def_KernelRankLean_Complexification
import Theorems.Thm_KernelRank_linearIndependent_ofReal
import Theorems.Thm_KernelRank_IsSumOfProducts_ofReal
import Theorems.Thm_KernelRank_ofReal_mem_rowSpan
import Theorems.Thm_KernelRank_finiteDimensional_rowSpan_ofReal
import Theorems.Thm_KernelRank_fin2Vec_one
import Theorems.Thm_KernelRank_fin2Vec_zero
import Theorems.Thm_KernelRank_finrank_rowSpan_le_of_isSumOfProducts
import Theorems.Thm_KernelRank_isSumOfProducts_finrank_rowSpan
attribute [local simp] KernelRank.fin2Vec_one
attribute [local simp] KernelRank.fin2Vec_zero



set_option autoImplicit true
open KernelRank
variable {α : Type*}
namespace KernelRank
theorem _root_.solution (K : (Fin 2 → α) → ℝ)
    [FiniteDimensional ℂ (rowSpan (fun z => (K z : ℂ)))] :
    Module.finrank ℝ (rowSpan K) =
      Module.finrank ℂ (rowSpan (fun z => (K z : ℂ))) := by
  let := finiteDimensional_rowSpan_ofReal K
  let b := Module.finBasis ℝ (rowSpan K)
  let v (i : Fin (Module.finrank ℝ (rowSpan K))) :
      rowSpan (fun z => (K z : ℂ)) :=
    ⟨fun x => ((b i : α → ℝ) x : ℂ), ofReal_mem_rowSpan (b i).2⟩
  have hb : LinearIndependent ℝ (fun i => (b i : α → ℝ)) :=
    b.linearIndependent.map' (rowSpan K).subtype (by simp)
  have hv : LinearIndependent ℂ v :=
    LinearIndependent.of_comp (rowSpan (fun z => (K z : ℂ))).subtype
      (linearIndependent_ofReal hb)
  refine le_antisymm ?_ ?_
  · simpa only [Fintype.card_fin] using hv.fintype_card_le_finrank
  · exact finrank_rowSpan_le_of_isSumOfProducts (isSumOfProducts_finrank_rowSpan K).ofReal
end KernelRank
