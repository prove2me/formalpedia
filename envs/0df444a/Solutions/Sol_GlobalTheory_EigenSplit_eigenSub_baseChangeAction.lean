-- Prove2me | solution 1 for GlobalTheory.EigenSplit.eigenSub_baseChangeAction
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:25:02.579858+00:00
-- url     : https://prove2.me/submissions/e46cf786-285c-4fa8-baee-35c1d6e30940

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_IsLocallyConstantRankAtStalkEigenSub
import Theorems.Thm_GlobalTheory_EigenSplit_coe_eigenBaseChangeEquiv_tmul
import Theorems.Thm_GlobalTheory_EigenSplit_coe_eigenBaseChangeEquiv
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
variable {O : Type*} [CommRing O] {R : Type*} [CommRing R] {ι : Type*}
  {N : Type*} [AddCommGroup N] [Module R N] {R' : Type*} [CommRing R'] [Algebra R R']
  {M : Type*} [AddCommGroup M] [Module R M] [Module R' M] [IsScalarTower R R' M]
  {ρ : O →+* Module.End R N} {ρ' : O →+* Module.End R' M} {f : N →ₗ[R] M}
variable {σ : ι → O →+* R}
variable (R') (ρ)
namespace GlobalTheory.EigenSplit
theorem _root_.solution [Finite ι] (h : IsSplitting σ) (i : ι) :
    eigenSub (baseChangeAction R' ρ) ((algebraMap R R').comp (σ i))
      = (eigenSub ρ (σ i)).baseChange R' := by
  ext y
  constructor
  · intro hy
    refine ⟨(eigenBaseChangeEquiv R' ρ h i).symm ⟨y, hy⟩, ?_⟩
    rw [← coe_eigenBaseChangeEquiv R' ρ h i, LinearEquiv.apply_symm_apply]
  · rintro ⟨t, rfl⟩
    rw [← coe_eigenBaseChangeEquiv R' ρ h i]
    exact Subtype.property _
end GlobalTheory.EigenSplit
