-- Prove2me | solution 1 for GlobalTheory.ReducedAlg.eq_zero_of_forall_lTensor_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:56:33.31788+00:00
-- url     : https://prove2.me/submissions/63e1fdd5-f3df-4ec6-88d5-4f92a020a894

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_EqZeroOfForallLTensorEqZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
open GlobalTheory GlobalTheory.ReducedAlg
namespace GlobalTheory.ReducedAlg
theorem _root_.solution {k : Type*} [Field k] {C M : Type*} [AddCommGroup C]
    [Module k C] [AddCommGroup M] [Module k M] {ι : Sort*} {N : ι → Type*}
    [∀ i, AddCommGroup (N i)] [∀ i, Module k (N i)] (φ : ∀ i, M →ₗ[k] N i)
    (hφ : ∀ m, (∀ i, φ i m = 0) → m = 0) (z : C ⊗[k] M)
    (hz : ∀ i, (φ i).lTensor C z = 0) : z = 0 := by
  classical
  let b := Module.Free.chooseBasis k C
  apply (TensorProduct.equivFinsuppOfBasisLeft b).injective
  rw [map_zero]
  ext j
  rw [Finsupp.coe_zero, Pi.zero_apply]
  have nat : ∀ (i : ι) (w : C ⊗[k] M),
      φ i (TensorProduct.equivFinsuppOfBasisLeft b w j) =
        TensorProduct.equivFinsuppOfBasisLeft b ((φ i).lTensor C w) j := by
    intro i w
    rw [TensorProduct.equivFinsuppOfBasisLeft_apply, TensorProduct.equivFinsuppOfBasisLeft_apply]
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul c m => simp
    | add x y hx hy => simp only [map_add, hx, hy]
  apply hφ
  intro i
  rw [nat, hz i, map_zero, Finsupp.coe_zero, Pi.zero_apply]
end GlobalTheory.ReducedAlg
