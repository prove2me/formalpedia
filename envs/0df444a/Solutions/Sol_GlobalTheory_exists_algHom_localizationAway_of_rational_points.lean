-- Prove2me | solution 1 for GlobalTheory.exists_algHom_localizationAway_of_rational_points
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:27:09.822037+00:00
-- url     : https://prove2.me/submissions/43fc26a5-ef98-4f81-8e65-623993b43ca4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsAlgHomLocalizationAwayOfRationalPoints
import Theorems.Thm_GlobalTheory_localizationAway_eq_zero_of_forall_eval

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Polynomial
namespace GlobalTheory
theorem _root_.solution :
    ∀ (k : Type) [Field k] [Infinite k] (A : Type) [CommRing A] [Algebra k A] (r : ℕ) (f : Fin r → A) (Pd : Polynomial k) (P : Fin r → Polynomial k) (ψ : k → (A →ₐ[k] k)), Algebra.adjoin k (Set.range f) = ⊤ → Pd ≠ 0 → (∀ t, t ≠ 0 → Pd.eval t ≠ 0 → ∀ i, ψ t (f i) * Pd.eval t = (P i).eval t) → ∃ χ : A →ₐ[k] Localization.Away (Polynomial.X * Pd), ∀ i, χ (f i) * algebraMap (Polynomial k) _ Pd = algebraMap (Polynomial k) _ (P i) := by
  intro k _ _ A _ _ r f Pd P ψ hf hPd hψ
  have hD : (Polynomial.X * Pd : Polynomial k) ≠ 0 := mul_ne_zero Polynomial.X_ne_zero hPd
  obtain ⟨u, hu⟩ : ∃ u : Localization.Away (Polynomial.X * Pd),
      u * algebraMap (Polynomial k) _ Pd = 1 := by
    have h := IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (Polynomial.X * Pd))
      (Polynomial.X * Pd)
    rw [map_mul] at h
    exact (isUnit_of_mul_isUnit_right h).exists_left_inv
  let Θ : MvPolynomial (Fin r) k →ₐ[k] Localization.Away (Polynomial.X * Pd) :=
    MvPolynomial.aeval fun i => algebraMap (Polynomial k) _ (P i) * u
  have hsurj : Function.Surjective (MvPolynomial.aeval f : MvPolynomial (Fin r) k →ₐ[k] A) := by
    rw [← AlgHom.range_eq_top, ← Algebra.adjoin_range_eq_range_aeval, hf]
  have hker : ∀ p, MvPolynomial.aeval f p = 0 → Θ p = 0 := by
    intro p hp
    apply localizationAway_eq_zero_of_forall_eval _ hD
    intro t ht e he
    rw [Polynomial.eval_mul, Polynomial.eval_X] at ht
    have ht0 : t ≠ 0 := left_ne_zero_of_mul ht
    have ht1 : Pd.eval t ≠ 0 := right_ne_zero_of_mul ht
    have key : ∀ p, e (Θ p) = ψ t (MvPolynomial.aeval f p) := by
      intro p
      induction p using MvPolynomial.induction_on with
      | C a =>
        rw [MvPolynomial.algHom_C, MvPolynomial.algHom_C, AlgHom.commutes,
          IsScalarTower.algebraMap_apply k (Polynomial k) (Localization.Away (Polynomial.X * Pd)),
          he]
        simp
      | add p q hp hq => simp only [map_add, hp, hq]
      | mul_X p i hp =>
        rw [map_mul, map_mul, map_mul, map_mul, hp]
        congr 1
        have h1 := congrArg e hu
        rw [map_mul, he, map_one] at h1
        simp only [Θ, MvPolynomial.aeval_X, map_mul, he]
        rw [← hψ t ht0 ht1 i, mul_assoc, mul_comm (Pd.eval t), h1, mul_one]
    rw [key, hp, map_zero]
  have hle : RingHom.ker (MvPolynomial.aeval f : MvPolynomial (Fin r) k →ₐ[k] A).toRingHom ≤
      RingHom.ker Θ.toRingHom := fun p hp => hker p hp
  refine ⟨AlgHom.liftOfSurjective _ hsurj Θ hle, fun i => ?_⟩
  have h2 : f i = MvPolynomial.aeval f (MvPolynomial.X i : MvPolynomial (Fin r) k) := by simp
  rw [h2]
  erw [AlgHom.liftOfSurjective_apply]
  simp only [Θ, MvPolynomial.aeval_X]
  rw [mul_assoc, hu, mul_one]
end GlobalTheory
