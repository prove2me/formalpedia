-- Prove2me | solution 1 for GlobalTheory.herm_form_identity
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:59:03.702089+00:00
-- url     : https://prove2.me/submissions/5ef6ff63-16ab-4e24-b868-13064c11600c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HermitianFormEqCombinationOfSelfAdjointIdentity

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (g : ℕ) (H₁ H₂ : Matrix (Fin g) (Fin g) ℂ)
    (γ : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ))
    (h1 : ∀ z w, z ⬝ᵥ H₂.mulVec (star w) = z ⬝ᵥ H₁.mulVec (star (γ w)))
    (h2 : ∀ z w, z ⬝ᵥ H₂.mulVec (star (γ w)) = γ z ⬝ᵥ H₂.mulVec (star w))
    (c₀ : ℚ) (r : ℕ) (c : Fin r → ℚ) (p : Fin r → Polynomial ℚ)
    (hid : (1 : Module.End ℂ (Fin g → ℂ)) = c₀ • γ + ∑ i, c i • ((Polynomial.aeval γ (p i)) ^ 2 * γ))
    (z w : Fin g → ℂ) :
    z ⬝ᵥ H₁.mulVec (star w) = (c₀ : ℂ) * (z ⬝ᵥ H₂.mulVec (star w)) +
      ∑ i, (c i : ℂ) * (Polynomial.aeval γ (p i) z ⬝ᵥ H₂.mulVec (star (Polynomial.aeval γ (p i) w))) := by
  have hadd : ∀ (H : Matrix (Fin g) (Fin g) ℂ) (z u v : Fin g → ℂ),
      z ⬝ᵥ H.mulVec (star (u + v)) = z ⬝ᵥ H.mulVec (star u) + z ⬝ᵥ H.mulVec (star v) := by
    intro H z u v; rw [star_add, mulVec_add, dotProduct_add]
  have hsmul : ∀ (H : Matrix (Fin g) (Fin g) ℂ) (z v : Fin g → ℂ) (a : ℚ),
      z ⬝ᵥ H.mulVec (star (a • v)) = (a : ℂ) * (z ⬝ᵥ H.mulVec (star v)) := by
    intro H z v a
    rw [← Rat.cast_smul_eq_qsmul ℂ, star_smul, mulVec_smul, dotProduct_smul, smul_eq_mul]
    simp
  have hsmulL : ∀ (H : Matrix (Fin g) (Fin g) ℂ) (z v : Fin g → ℂ) (a : ℚ),
      (a • z) ⬝ᵥ H.mulVec (star v) = (a : ℂ) * (z ⬝ᵥ H.mulVec (star v)) := by
    intro H z v a
    rw [← Rat.cast_smul_eq_qsmul ℂ, smul_dotProduct, smul_eq_mul]
  have hsum : ∀ (H : Matrix (Fin g) (Fin g) ℂ) (z : Fin g → ℂ) (f : Fin r → (Fin g → ℂ)),
      z ⬝ᵥ H.mulVec (star (∑ i, f i)) = ∑ i, z ⬝ᵥ H.mulVec (star (f i)) := by
    intro H z f
    rw [star_sum, mulVec_sum, dotProduct_sum]
  have hsa : ∀ (q : Polynomial ℚ) (z w : Fin g → ℂ),
      z ⬝ᵥ H₂.mulVec (star (Polynomial.aeval γ q w)) =
        Polynomial.aeval γ q z ⬝ᵥ H₂.mulVec (star w) := by
    intro q
    induction q using Polynomial.induction_on with
    | C a =>
      intro z w
      simp only [Polynomial.aeval_C, Module.algebraMap_end_apply]
      rw [hsmul, hsmulL]
    | add p q hp hq =>
      intro z w
      simp only [map_add, LinearMap.add_apply]
      rw [hadd, hp, hq, add_dotProduct]
    | monomial n a ih =>
      intro z w
      have e : Polynomial.C a * Polynomial.X ^ (n+1) =
          (Polynomial.C a * Polynomial.X ^ n) * Polynomial.X := by ring
      have e' : Polynomial.C a * Polynomial.X ^ (n+1) =
          Polynomial.X * (Polynomial.C a * Polynomial.X ^ n) := by ring
      calc z ⬝ᵥ H₂.mulVec (star (Polynomial.aeval γ (Polynomial.C a * Polynomial.X ^ (n+1)) w))
          = z ⬝ᵥ H₂.mulVec (star (Polynomial.aeval γ (Polynomial.C a * Polynomial.X ^ n) (γ w))) := by
            rw [e, map_mul (Polynomial.aeval γ) (Polynomial.C a * Polynomial.X ^ n) Polynomial.X,
              Polynomial.aeval_X, Module.End.mul_apply]
        _ = Polynomial.aeval γ (Polynomial.C a * Polynomial.X ^ n) z ⬝ᵥ H₂.mulVec (star (γ w)) :=
            ih _ _
        _ = γ (Polynomial.aeval γ (Polynomial.C a * Polynomial.X ^ n) z) ⬝ᵥ H₂.mulVec (star w) :=
            h2 _ _
        _ = _ := by
            rw [e', map_mul (Polynomial.aeval γ) Polynomial.X (Polynomial.C a * Polynomial.X ^ n),
              Polynomial.aeval_X, Module.End.mul_apply]
  have comm : ∀ q : Polynomial ℚ, (Polynomial.aeval γ q) ^ 2 * γ =
      γ * (Polynomial.aeval γ q * Polynomial.aeval γ q) := by
    intro q
    rw [show (Polynomial.aeval γ q) ^ 2 * γ = Polynomial.aeval γ (q ^ 2 * Polynomial.X) by
          simp [map_mul, map_pow],
      show q ^ 2 * Polynomial.X = Polynomial.X * (q * q) by ring]
    simp [map_mul]
  have hw : w = c₀ • γ w + ∑ i, c i • (γ (Polynomial.aeval γ (p i) (Polynomial.aeval γ (p i) w))) := by
    have := congrArg (fun f : Module.End ℂ (Fin g → ℂ) => f w) hid
    simp only [Module.End.one_apply, LinearMap.add_apply, LinearMap.smul_apply,
      comm] at this
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, Module.End.mul_apply] at this
    exact this
  conv_lhs => rw [hw]
  rw [hadd, hsmul, hsum, ← h1]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hsmul, ← h1, hsa]
end GlobalTheory
