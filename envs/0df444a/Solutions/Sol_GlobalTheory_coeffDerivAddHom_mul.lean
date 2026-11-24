-- Prove2me | solution 1 for GlobalTheory.coeffDerivAddHom_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:31:47.097303+00:00
-- url     : https://prove2.me/submissions/06cca975-effa-4b0a-9731-179929a1d4c4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DerivationExtendMvPolynomial
import Theorems.Thm_GlobalTheory_coeffDerivAddHom_monomial

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
namespace GlobalTheory
theorem _root_.solution {B τ : Type} [CommRing B] (D : Derivation ℤ B B)
    (p q : MvPolynomial τ B) :
    coeffDerivAddHom D (p * q) = p * coeffDerivAddHom D q + q * coeffDerivAddHom D p := by
  induction p using MvPolynomial.induction_on' with
  | monomial u a =>
    induction q using MvPolynomial.induction_on' with
    | monomial v b =>
      simp only [MvPolynomial.monomial_mul, coeffDerivAddHom_monomial, Derivation.leibniz,
        smul_eq_mul, map_add, add_comm v u]
    | add q₁ q₂ h₁ h₂ =>
      rw [mul_add, map_add, h₁, h₂, map_add]; ring
  | add p₁ p₂ h₁ h₂ =>
    rw [add_mul, map_add, h₁, h₂, map_add]; ring
end GlobalTheory
