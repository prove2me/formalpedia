-- Prove2me | solution 1 for GlobalTheory.derivation_sumAlgEquiv_eq_pderiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:33:43.991215+00:00
-- url     : https://prove2.me/submissions/f4b5b61c-b345-4e8a-be0b-ed58fd804349

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsGenericJacobianDataOfPrimeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsGenericJacobianDataIterated

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing TensorProduct
open GlobalTheory
open MvPolynomial
namespace GlobalTheory
theorem _root_.solution {Λ : Type} [CommRing Λ] {σ τ : Type}
    (d : τ ⊕ σ → Derivation ℤ (MvPolynomial τ (MvPolynomial σ Λ))
      (MvPolynomial τ (MvPolynomial σ Λ)))
    (h1 : ∀ t x, d (Sum.inl t) x = pderiv t x)
    (h2 : ∀ s x, d (Sum.inr s) (C x) = C (pderiv s x))
    (h3 : ∀ s t, d (Sum.inr s) (X t) = 0) (u : τ ⊕ σ) (y : MvPolynomial (τ ⊕ σ) Λ) :
    d u (sumAlgEquiv Λ τ σ y) = sumAlgEquiv Λ τ σ (pderiv u y) := by
  classical
  have eC : ∀ a : Λ, sumAlgEquiv Λ τ σ (C a) = C (C a) := fun a => by
    simp [sumAlgEquiv_C_inl]
  have eL : ∀ t : τ, sumAlgEquiv Λ τ σ (X (Sum.inl t)) = X t := fun t => by
    simp [sumAlgEquiv_X_inl]
  have eR : ∀ s : σ, sumAlgEquiv Λ τ σ (X (Sum.inr s)) = C (X s) := fun s => by
    simp [sumAlgEquiv_X_inr]
  have hX : ∀ v : τ ⊕ σ,
      d u (sumAlgEquiv Λ τ σ (X v)) = sumAlgEquiv Λ τ σ (pderiv u (X v)) := by
    intro v
    rcases u with t | s <;> rcases v with t' | s'
    · rw [eL, h1]
      by_cases h : t = t'
      · subst h; simp
      · rw [pderiv_X_of_ne (Ne.symm h), pderiv_X_of_ne (by simpa using Ne.symm h), map_zero]
    · rw [eR, h1, pderiv_C, pderiv_X_of_ne (by simp), map_zero]
    · rw [eL, h3, pderiv_X_of_ne (by simp), map_zero]
    · rw [eR, h2]
      by_cases h : s = s'
      · subst h; simp
      · rw [pderiv_X_of_ne (Ne.symm h), pderiv_X_of_ne (by simpa using Ne.symm h), map_zero,
          map_zero]
  induction y using MvPolynomial.induction_on with
  | C a =>
    rw [eC, pderiv_C, map_zero]
    rcases u with t | s
    · rw [h1, pderiv_C]
    · rw [h2, pderiv_C, map_zero]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p v hp =>
    rw [map_mul, Derivation.leibniz, Derivation.leibniz, hp, hX, map_add, smul_eq_mul,
      smul_eq_mul, smul_eq_mul, smul_eq_mul, map_mul, map_mul]
end GlobalTheory
