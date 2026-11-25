-- Prove2me | solution 1 for GlobalTheory.T.exists_skewHermitian_mul_add_det_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:53:36.308537+00:00
-- url     : https://prove2.me/submissions/e1a3b1ad-7a0d-4b3a-bedd-82e44a9e9b29

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSkewHermitianMulAddDetNeZeroOfPair
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSkewHermitianMulAddDetNeZeroOfPairStatement
import Theorems.Thm_GlobalTheory_exists_skewHermitian_mul_add_det_ne_zero_of_pair


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
    ∀ (n : ℕ) (C D : Matrix (Fin n) (Fin n) k), C * (D.map σ)ᵀ + D * (C.map σ)ᵀ = 0 →
    (∀ a : Fin n → k, a ᵥ* C = 0 → a ᵥ* D = 0 → a = 0) →
      ∃ V : Matrix (Fin n) (Fin n) k, (V.map σ)ᵀ = -V ∧ (C * V + D).det ≠ 0 := by
  first | exact @GlobalTheory.exists_skewHermitian_mul_add_det_ne_zero_of_pair | exact GlobalTheory.exists_skewHermitian_mul_add_det_ne_zero_of_pair | (intros; apply GlobalTheory.exists_skewHermitian_mul_add_det_ne_zero_of_pair <;> assumption)
end _root_.GlobalTheory.T
