-- Prove2me | solution 1 for GlobalTheory.T.exists_skewHermitian_det_mul_add_ne_zero_of_idempotent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:39:21.285314+00:00
-- url     : https://prove2.me/submissions/eba10041-589e-4acb-b08c-d523fdb6bc29

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SkewHermitianPerturbIdempotentDetNeZero
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SkewHermitianPerturbIdempotentDetNeZeroStatement
import Theorems.Thm_GlobalTheory_skewHermitian_perturb_idempotent_det_ne_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped Matrix
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (k : Type) [Field k] (σ : k →+* k), (∀ x, σ (σ x) = x) → ∀ ε : k, ε ≠ 0 → σ ε = -ε →
    ∀ (n : ℕ) (E D : Matrix (Fin n) (Fin n) k), E * E = E → (E.map σ)ᵀ = E → E * (D.map σ)ᵀ + D * E = 0 →
    (∀ a : Fin n → k, a ᵥ* E = 0 → a ᵥ* D = 0 → a = 0) →
      ∃ V : Matrix (Fin n) (Fin n) k, (V.map σ)ᵀ = -V ∧ (E * V + D).det ≠ 0 := by
  first | exact @GlobalTheory.skewHermitian_perturb_idempotent_det_ne_zero | exact GlobalTheory.skewHermitian_perturb_idempotent_det_ne_zero | (intros; apply GlobalTheory.skewHermitian_perturb_idempotent_det_ne_zero <;> assumption)
end _root_.GlobalTheory.T
