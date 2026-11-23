-- Prove2me | solution 1 for GlobalTheory.EigenSplit.coe_eigenBaseChangeEquiv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:34:22.857393+00:00
-- url     : https://prove2.me/submissions/2ac04c5c-cc44-4268-a334-6ee0f9ad9113

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_IsLocallyConstantRankAtStalkEigenSub
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
variable {O : Type*} [CommRing O] {R : Type*} [CommRing R] {ι : Type*}
  {N : Type*} [AddCommGroup N] [Module R N] {R' : Type*} [CommRing R'] [Algebra R R']
  {M : Type*} [AddCommGroup M] [Module R M] [Module R' M] [IsScalarTower R R' M]
  {ρ : O →+* Module.End R N} {ρ' : O →+* Module.End R' M} {f : N →ₗ[R] M}
variable {σ : ι → O →+* R}
variable (R') (ρ)
namespace GlobalTheory.EigenSplit
theorem _root_.solution [Finite ι] (h : IsSplitting σ) (i : ι)
    (t : R' ⊗[R] eigenSub ρ (σ i)) :
    (eigenBaseChangeEquiv R' ρ h i t : R' ⊗[R] N)
      = (eigenSub ρ (σ i)).subtype.baseChange R' t := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul r x => simp
  | add s t hs ht => simp [hs, ht]
end GlobalTheory.EigenSplit
