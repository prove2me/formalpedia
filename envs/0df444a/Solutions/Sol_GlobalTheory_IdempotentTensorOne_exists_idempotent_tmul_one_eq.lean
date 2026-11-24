-- Prove2me | solution 1 for GlobalTheory.IdempotentTensorOne.exists_idempotent_tmul_one_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:55:17.099101+00:00
-- url     : https://prove2.me/submissions/f3167a00-196d-4c68-9ef9-506b7fd4247d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsIntegralOfIsIdempotentElem
import Theorems.Thm_GlobalTheory_IdempotentTensorOne_isIntegral_of_isIdempotentElem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
open GlobalTheory GlobalTheory.IdempotentTensorOne
namespace GlobalTheory.IdempotentTensorOne
theorem _root_.solution (R A : Type) [CommRing R] [IsDomain R]
    [IsIntegrallyClosed R] [CommRing A] [Algebra R A] (hA : Algebra.Smooth R A)
    (ε : A ⊗[R] FractionRing R) (hε : IsIdempotentElem ε) :
    ∃ a : A, IsIdempotentElem a ∧ a ⊗ₜ[R] (1 : FractionRing R) = ε := by
  have : Algebra.Smooth R A := hA

  have hint : ε ∈ integralClosure A (A ⊗[R] FractionRing R) := isIntegral_of_isIdempotentElem hε
  obtain ⟨t, ht⟩ := (TensorProduct.toIntegralClosure_bijective_of_smooth
    (R := R) (S := A) (B := FractionRing R)).2 ⟨ε, hint⟩
  have hε' : Algebra.TensorProduct.map (AlgHom.id A A) (integralClosure R (FractionRing R)).val t = ε :=
    congrArg Subtype.val ht
  have hdesc : ∀ u : A ⊗[R] integralClosure R (FractionRing R), ∃ a : A,
      a ⊗ₜ[R] (1 : FractionRing R) =
        Algebra.TensorProduct.map (AlgHom.id A A) (integralClosure R (FractionRing R)).val u := by
    intro u
    induction u using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | tmul x y =>
      obtain ⟨r, hr⟩ := (IsIntegrallyClosed.isIntegral_iff (R := R) (K := FractionRing R)).1
        ((mem_integralClosure_iff _ _).1 y.2)
      refine ⟨r • x, ?_⟩
      rw [Algebra.TensorProduct.map_tmul, TensorProduct.smul_tmul, ← Algebra.algebraMap_eq_smul_one, hr]
      rfl
    | add u w hu hw =>
      obtain ⟨a, ha⟩ := hu
      obtain ⟨b, hb⟩ := hw
      exact ⟨a + b, by rw [TensorProduct.add_tmul, ha, hb, map_add]⟩
  obtain ⟨a, ha⟩ := hdesc t
  rw [hε'] at ha
  refine ⟨a, ?_, ha⟩

  have hinj : Function.Injective (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] FractionRing R) :=
    Algebra.TensorProduct.includeLeft_injective (IsFractionRing.injective R (FractionRing R))
  apply hinj
  show (a * a) ⊗ₜ[R] (1 : FractionRing R) = a ⊗ₜ[R] (1 : FractionRing R)
  rw [← mul_one (1 : FractionRing R), ← Algebra.TensorProduct.tmul_mul_tmul, mul_one, ha, hε.eq]
end GlobalTheory.IdempotentTensorOne
