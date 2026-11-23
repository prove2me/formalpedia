-- Prove2me | solution 1 for GlobalTheory.EigenSplit.isInternal_eigenSub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:34:48.168046+00:00
-- url     : https://prove2.me/submissions/e0c5c187-5985-4a35-82df-b12c2c76b714

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_IsLocallyConstantRankAtStalkEigenSub

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct NumberField
open Polynomial
open GlobalTheory
open GlobalTheory.EigenSplit
variable {O : Type*} [CommRing O] {R : Type*} [CommRing R] {ι : Type*}
  {N : Type*} [AddCommGroup N] [Module R N] {N' : Type*} [AddCommGroup N'] [Module R N']
  {N'' : Type*} [AddCommGroup N''] [Module R N'']
variable [DecidableEq ι] {σ : ι → O →+* R} (h : IsSplitting σ) (ρ : O →+* Module.End R N)
include h
namespace GlobalTheory.EigenSplit
theorem _root_.solution [Finite ι] : DirectSum.IsInternal fun i => eigenSub ρ (σ i) := by
  have := Fintype.ofFinite ι
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
  constructor
  · intro i
    rw [Submodule.disjoint_def]
    intro x hx hx'
    rw [← proj_of_mem h hx]
    have : (⨆ j, ⨆ (_ : j ≠ i), eigenSub ρ (σ j)) ≤ LinearMap.ker (proj h ρ i) :=
      iSup₂_le fun j hj y hy => proj_of_mem_ne h hj hy
    exact this hx'
  · rw [eq_top_iff]
    intro x _
    rw [← sum_proj h ρ x]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.mem_iSup_of_mem i (proj_mem h ρ i x)
end GlobalTheory.EigenSplit
