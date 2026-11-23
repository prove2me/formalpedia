-- Prove2me | solution 1 for GlobalTheory.EigenSplit.charpoly_eq_prod
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:38:15.075591+00:00
-- url     : https://prove2.me/submissions/c80b7ab0-f9ac-46b9-8c1c-7e96544b15cb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_IsLocallyConstantRankAtStalkEigenSub
import Theorems.Thm_GlobalTheory_EigenSplit_isInternal_eigenSub
import Theorems.Thm_GlobalTheory_EigenSplit_finite_eigenSub
import Theorems.Thm_GlobalTheory_EigenSplit_coe_eigenBaseChangeEquiv_tmul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.EigenSplit.coe_eigenBaseChangeEquiv_tmul

set_option autoImplicit false
open scoped TensorProduct NumberField
open Polynomial
open GlobalTheory
open GlobalTheory.EigenSplit
variable {O : Type*} [CommRing O] {R : Type*} [CommRing R] {ι : Type*} [Fintype ι]
  {N : Type*} [AddCommGroup N] [Module R N]
variable {σ : ι → O →+* R} (h : IsSplitting σ) (ρ : O →+* Module.End R N)
  [Module.Free R N] [Module.Finite R N]
include h
namespace GlobalTheory.EigenSplit
theorem _root_.solution (hfree : ∀ i, Module.Free R (eigenSub ρ (σ i))) (a : O) :
    (ρ a).charpoly = ∏ i, (X - C (σ i a)) ^ Module.finrank R (eigenSub ρ (σ i)) := by
  classical
  nontriviality R
  have hfin := fun i => finite_eigenSub h ρ i
  let b := (isInternal_eigenSub h ρ).collectedBasis
    fun i => Module.Free.chooseBasis R (eigenSub ρ (σ i))
  have hm : LinearMap.toMatrix b b (ρ a) = Matrix.diagonal fun k => σ k.1 a := by
    ext k l
    have hl : b l ∈ eigenSub ρ (σ l.1) := (isInternal_eigenSub h ρ).collectedBasis_mem _ l
    rw [LinearMap.toMatrix_apply, mem_eigenSub.1 hl a]
    rcases eq_or_ne k l with rfl | hkl
    · simp
    · simp [hkl]
  rw [← LinearMap.charpoly_toMatrix (ρ a) b, hm, Matrix.charpoly_diagonal, Fintype.prod_sigma]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp [Module.finrank_eq_card_chooseBasisIndex]
end GlobalTheory.EigenSplit
