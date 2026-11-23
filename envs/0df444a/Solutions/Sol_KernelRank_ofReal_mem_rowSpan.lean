-- Prove2me | solution 1 for KernelRank.ofReal_mem_rowSpan
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:26:29.70365+00:00
-- url     : https://prove2.me/submissions/3d7bde7b-492e-4bcf-9fd7-2c06e96f446c

import Definitions.Def_KernelRankLean_RowSpan
import Definitions.Def_KernelRankLean_Complexification
import Theorems.Thm_KernelRank_IsSumOfProducts_add
import Theorems.Thm_KernelRank_fin2Vec_one
import Theorems.Thm_KernelRank_fin2Vec_zero
import Theorems.Thm_KernelRank_row_mem_rowSpan
attribute [local simp] KernelRank.fin2Vec_one
attribute [local simp] KernelRank.fin2Vec_zero



set_option autoImplicit true
open KernelRank
variable {α : Type*}
namespace KernelRank
theorem _root_.solution {K : (Fin 2 → α) → ℝ} {f : α → ℝ} (hf : f ∈ rowSpan K) :
    (fun x => (f x : ℂ)) ∈ rowSpan (fun z => (K z : ℂ)) := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨y, rfl⟩ := hf
    exact row_mem_rowSpan _ y
  | zero =>
    exact (rowSpan (fun z => (K z : ℂ))).zero_mem
  | add f g _ _ hf hg =>
    convert Submodule.add_mem _ hf hg using 1
    ext x
    simp
  | smul a f _ hf =>
    convert Submodule.smul_mem (rowSpan (fun z => (K z : ℂ))) (a : ℂ) hf using 1
    ext x
    simp
end KernelRank
