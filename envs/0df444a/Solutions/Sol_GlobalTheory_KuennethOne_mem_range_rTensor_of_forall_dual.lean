-- Prove2me | solution 1 for GlobalTheory.KuennethOne.mem_range_rTensor_of_forall_dual
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:33:52.019831+00:00
-- url     : https://prove2.me/submissions/e816bf36-03e5-402a-9a81-6500c8eb6182

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitsOfIsAffineOpen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_MemRangeRTensorOfForallDual
import Theorems.Thm_GlobalTheory_KuennethOne_appLE_rs
import Theorems.Thm_GlobalTheory_KuennethOne_rs_appLE
import Theorems.Thm_GlobalTheory_KuennethOne_rs_rs
import Theorems.Thm_GlobalTheory_KuennethOne_rs_self
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.KuennethOne.appLE_rs
attribute [local simp] GlobalTheory.KuennethOne.rs_appLE
attribute [local simp] GlobalTheory.KuennethOne.rs_rs
attribute [local simp] GlobalTheory.KuennethOne.rs_self



set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace TensorProduct
open GlobalTheory GlobalTheory.KuennethOne
namespace GlobalTheory.KuennethOne
theorem _root_.solution {R C₀ C₁ B : Type} [CommRing R] (hR : IsField R)
    [AddCommGroup C₀] [Module R C₀] [AddCommGroup C₁] [Module R C₁] [AddCommGroup B] [Module R B]
    (δ : C₀ →ₗ[R] C₁) (z : C₁ ⊗[R] B)
    (h : ∀ l : C₁ →ₗ[R] R, l ∘ₗ δ = 0 → TensorProduct.lid R B (l.rTensor B z) = 0) :
    ∃ y, δ.rTensor B y = z := by
  classical
  letI := hR.toField
  have hex := rTensor_exact B (LinearMap.exact_map_mkQ_range δ) (Submodule.mkQ_surjective _)
  refine (hex z).mp ?_
  let b := Module.Basis.ofVectorSpace R (C₁ ⧸ LinearMap.range δ)
  apply (TensorProduct.equivFinsuppOfBasisLeft b).injective
  ext i
  have h1 := h (b.coord i ∘ₗ (LinearMap.range δ).mkQ) (by
    ext x
    simp [(Submodule.Quotient.mk_eq_zero _).mpr (LinearMap.mem_range_self δ x)])
  rw [map_zero, Finsupp.zero_apply, ← h1]
  clear h h1
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]
end GlobalTheory.KuennethOne
