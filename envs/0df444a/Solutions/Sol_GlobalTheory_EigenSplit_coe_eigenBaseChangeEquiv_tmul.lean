-- Prove2me | solution 1 for GlobalTheory.EigenSplit.coe_eigenBaseChangeEquiv_tmul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:53:47.986831+00:00
-- url     : https://prove2.me/submissions/b51ab563-43d7-44d1-963b-b0977258a845

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
  {N : Type*} [AddCommGroup N] [Module R N] {R' : Type*} [CommRing R'] [Algebra R R']
  {M : Type*} [AddCommGroup M] [Module R M] [Module R' M] [IsScalarTower R R' M]
  {ρ : O →+* Module.End R N} {ρ' : O →+* Module.End R' M} {f : N →ₗ[R] M}
variable {σ : ι → O →+* R}
variable (R') (ρ)
namespace GlobalTheory.EigenSplit
theorem _root_.solution [Finite ι] (h : IsSplitting σ) (i : ι) (r : R')
    (x : eigenSub ρ (σ i)) :
    (eigenBaseChangeEquiv R' ρ h i (r ⊗ₜ x) : R' ⊗[R] N) = r ⊗ₜ (x : N) := by
  simp [eigenBaseChangeEquiv, IsBaseChange.equiv_tmul, TensorProduct.smul_tmul']
end GlobalTheory.EigenSplit
