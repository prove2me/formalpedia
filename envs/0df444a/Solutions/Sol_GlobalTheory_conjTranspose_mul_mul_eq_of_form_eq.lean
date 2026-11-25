-- Prove2me | solution 1 for GlobalTheory.conjTranspose_mul_mul_eq_of_form_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:11:39.360624+00:00
-- url     : https://prove2.me/submissions/82a75e7d-c9b8-4563-9c1e-8ffa5ddfb432

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsUnitaryMulVecEqOfFormEq

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
theorem _root_.solution {E : Type} [Field E] [StarRing E] {n : ℕ}
    (J γ : Matrix (Fin n) (Fin n) E)
    (h : ∀ z w : Fin n → E, star (γ *ᵥ z) ⬝ᵥ (J *ᵥ (γ *ᵥ w)) = star z ⬝ᵥ (J *ᵥ w)) :
    γᴴ * J * γ = J := by
  have key : ∀ z w : Fin n → E, star z ⬝ᵥ ((γᴴ * J * γ) *ᵥ w) = star z ⬝ᵥ (J *ᵥ w) := by
    intro z w
    rw [← h z w, star_mulVec, ← dotProduct_mulVec, ← mulVec_mulVec, ← mulVec_mulVec]
  ext i j
  simpa [single_dotProduct, mulVec_single_one] using key (star (Pi.single i 1)) (Pi.single j 1)
end GlobalTheory
