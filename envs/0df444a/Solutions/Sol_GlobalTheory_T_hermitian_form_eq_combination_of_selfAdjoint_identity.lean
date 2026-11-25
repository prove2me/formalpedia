-- Prove2me | solution 1 for GlobalTheory.T.hermitian_form_eq_combination_of_selfAdjoint_identity
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:21:27.555192+00:00
-- url     : https://prove2.me/submissions/836c1804-3bec-4259-b6a7-d4e2450f8b60

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HermitianFormEqCombinationOfSelfAdjointIdentity
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HermitianFormEqCombinationOfSelfAdjointIdentityStatement
import Theorems.Thm_GlobalTheory_herm_form_identity


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (g : ℕ) (H₁ H₂ : Matrix (Fin g) (Fin g) ℂ) (γ : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)),
    (∀ z w, z ⬝ᵥ H₂.mulVec (star w) = z ⬝ᵥ H₁.mulVec (star (γ w))) →
    (∀ z w, z ⬝ᵥ H₂.mulVec (star (γ w)) = γ z ⬝ᵥ H₂.mulVec (star w)) →
    ∀ (c₀ : ℚ) (r : ℕ) (c : Fin r → ℚ) (p : Fin r → Polynomial ℚ),
    (1 : Module.End ℂ (Fin g → ℂ)) = c₀ • γ + ∑ i, c i • ((Polynomial.aeval γ (p i)) ^ 2 * γ) →
    ∀ z w : Fin g → ℂ, z ⬝ᵥ H₁.mulVec (star w) = (c₀ : ℂ) * (z ⬝ᵥ H₂.mulVec (star w)) +
      ∑ i, (c i : ℂ) * (Polynomial.aeval γ (p i) z ⬝ᵥ H₂.mulVec (star (Polynomial.aeval γ (p i) w))) := by
  first | exact @GlobalTheory.herm_form_identity | exact GlobalTheory.herm_form_identity | (intros; apply GlobalTheory.herm_form_identity <;> assumption)
end _root_.GlobalTheory.T
