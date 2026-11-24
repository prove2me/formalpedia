-- Prove2me | solution 1 for GlobalTheory.existsUnique_algHom_of_compatible_tensor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:57:39.222599+00:00
-- url     : https://prove2.me/submissions/6dea36d6-5900-4957-bd84-ccf739ae1ac6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueAlgEquivOfCompatibleQuotient
import Theorems.Thm_GlobalTheory_isAdicComplete_of_finite
import Theorems.Thm_GlobalTheory_existsUnique_algHom_of_compatible_tower
import Theorems.Thm_GlobalTheory_one_tmul_quotient_eq_zero_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory
open TensorProduct
variable {R : Type*} [CommRing R] (I : Ideal R)
variable [IsNoetherianRing R] [IsAdicComplete I R]
variable {A B : Type*} [Ring A] [Ring B] [Algebra R A] [Algebra R B]
namespace GlobalTheory
theorem _root_.solution [Module.Finite R B]
    (f : ∀ n : ℕ, (R ⧸ I ^ n) ⊗[R] A →ₐ[R ⧸ I ^ n] (R ⧸ I ^ n) ⊗[R] B)
    (hf : ∀ n x, adicTensorTransition I B n (f (n + 1) x) = f n (adicTensorTransition I A n x)) :
    ∃! g : A →ₐ[R] B, ∀ n a, (1 : R ⧸ I ^ n) ⊗ₜ[R] g a = f n (1 ⊗ₜ a) :=
  have := isAdicComplete_of_finite I B
  existsUnique_algHom_of_compatible_tower I (fun _ ↦ Algebra.TensorProduct.includeRight)
    (fun n x ↦ by
      obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective _ (quotTensorEquivQuotSMul B (I ^ n) x)
      exact ⟨y, by rw [← (quotTensorEquivQuotSMul B (I ^ n)).symm_apply_apply x, ← hy]; rfl⟩)
    (fun n x ↦ one_tmul_quotient_eq_zero_iff _ x)
    (fun n ↦ adicTensorTransition I B n) (fun _ _ ↦ by simp)
    (fun n ↦ ((f n).restrictScalars R).comp Algebra.TensorProduct.includeRight)
    (fun n _ ↦ (hf n _).trans (by simp))
end GlobalTheory
