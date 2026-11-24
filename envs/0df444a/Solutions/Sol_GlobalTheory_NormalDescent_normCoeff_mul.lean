-- Prove2me | solution 1 for GlobalTheory.NormalDescent.normCoeff_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:31:01.648532+00:00
-- url     : https://prove2.me/submissions/6e7ecacf-ec19-41f1-b606-f763db678be4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_AlgebraMapNormCoeff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ReversedCharpolyCoeffInDomainMul
import Theorems.Thm_GlobalTheory_NormalDescent_charpoly_reverse_coeff_smul
import Theorems.Thm_GlobalTheory_NormalDescent_exists_charK_coeff
import Theorems.Thm_GlobalTheory_NormalDescent_algebraMap_normCoeff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory Polynomial TensorProduct
open GlobalTheory GlobalTheory.NormalDescent
namespace GlobalTheory.NormalDescent
theorem _root_.solution : ∀ {A B : Type} [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [CommRing B] (φ : A →+* B)
    (hφ : φ.Finite) (u : A) (b : B) (k : ℕ), normCoeff φ hφ (φ u * b) k = u ^ k * normCoeff φ hφ b k := by
  intro A B _ _ _ _ φ hφ u b k
  have hrev : ∀ b' : B, ∃ a : A, algebraMap A (FractionRing A) a = (charK φ hφ (FractionRing A) b').reverse.coeff k :=
    fun b' => by rw [coeff_reverse]; exact exists_charK_coeff φ hφ b' _
  have key : (charK φ hφ (FractionRing A) (φ u * b)).reverse.coeff k
      = (algebraMap A (FractionRing A) u) ^ k * (charK φ hφ (FractionRing A) b).reverse.coeff k := by
    letI := φ.toAlgebra
    haveI : Module.Finite A B := hφ
    haveI : Module.Free (FractionRing A) (FractionRing A ⊗[A] B) := Module.Free.of_divisionRing _ _
    have e1 : (1 : FractionRing A) ⊗ₜ[A] (φ u * b)
        = algebraMap A (FractionRing A) u • ((1 : FractionRing A) ⊗ₜ[A] b) := by
      rw [algebraMap_smul, ← tmul_smul, Algebra.smul_def]; rfl
    show (Algebra.lmul _ _ ((1 : FractionRing A) ⊗ₜ[A] (φ u * b))).charpoly.reverse.coeff k = _
    rw [e1, map_smul]
    exact charpoly_reverse_coeff_smul _ _ _
  apply IsFractionRing.injective A (FractionRing A)
  rw [map_mul, map_pow, algebraMap_normCoeff _ _ _ _ (hrev _), algebraMap_normCoeff _ _ _ _ (hrev _), key]
end GlobalTheory.NormalDescent
