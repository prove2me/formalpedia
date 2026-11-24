-- Prove2me | solution 1 for GlobalTheory.dot_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:36:02.464441+00:00
-- url     : https://prove2.me/submissions/9eb16864-0fca-4fcb-9372-67b403a56c46

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_SchurComplementBlockQuadraticLowerBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ComplexOrder
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (n : ℕ) (x v : Fin n → ℝ) : (x ⬝ᵥ v) ^ 2 ≤ (x ⬝ᵥ x) * (v ⬝ᵥ v) := by
  have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ x v
  simpa [dotProduct, sq] using this
end GlobalTheory
