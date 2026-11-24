-- Prove2me | solution 1 for GlobalTheory.ClassParam.hlin_surj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:27:40.711829+00:00
-- url     : https://prove2.me/submissions/149b1303-2123-4e3b-8e41-a723c6d119f2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_PlusPolynomialInclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LeftMulMatrixTransfer

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial TensorProduct Matrix Formalism.UG
open GlobalTheory GlobalTheory.ClassParam
variable {A : Type} [CommRing A] {r : ℕ} (σ : A →+* A)
namespace GlobalTheory.ClassParam
theorem _root_.solution (hσ : ∀ a, σ (σ a) = a) {J : Matrix (Fin r) (Fin r) A} (hJ : IsUnit J.det)
    (f : (Fin r → A) →ₗ[A] A) : ∃ x, ∀ y, hform σ J x y = f y := by
  refine ⟨σ ∘ ((fun i => f (Pi.single i 1)) ᵥ* J⁻¹), fun y => ?_⟩
  have : σ ∘ σ ∘ ((fun i => f (Pi.single i 1)) ᵥ* J⁻¹) = (fun i => f (Pi.single i 1)) ᵥ* J⁻¹ :=
    funext fun i => hσ _
  rw [hform_eq, this, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hJ,
    Matrix.vecMul_one, LinearMap.pi_apply_eq_sum_univ f y]
  refine Finset.sum_congr rfl fun i _ => ?_
  have : (fun j => if i = j then (1 : A) else 0) = Pi.single i 1 := by
    ext j; simp [Pi.single_apply, eq_comm]
  rw [smul_eq_mul, mul_comm, this]
end GlobalTheory.ClassParam
