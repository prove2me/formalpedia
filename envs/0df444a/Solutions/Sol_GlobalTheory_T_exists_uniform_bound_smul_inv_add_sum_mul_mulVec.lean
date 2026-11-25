-- Prove2me | solution 1 for GlobalTheory.T.exists_uniform_bound_smul_inv_add_sum_mul_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:19:52.256971+00:00
-- url     : https://prove2.me/submissions/fa746aba-a4ce-49fe-99cd-5d8f6edf7327

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SmulInvMulPosSemidefUniformBound
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SmulInvMulPosSemidefUniformBoundStatement
import Theorems.Thm_GlobalTheory_smul_inv_mul_posSemidef_uniform_bound


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ComplexOrder Matrix
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (g a : ℕ) (B : Fin a → Matrix (Fin g) (Fin g) ℝ) (c C : ℝ), 0 < c → (∀ i, (B i).PosSemidef) → ∃ W : ℝ, ∀ (Y' : Matrix (Fin g) (Fin g) ℝ) (t : Fin a → ℝ), Y'.IsSymm → (∀ x, c * (x ⬝ᵥ x) ≤ x ⬝ᵥ Y'.mulVec x) → (∀ x, x ⬝ᵥ Y'.mulVec x ≤ C * (x ⬝ᵥ x)) → (∀ i, 0 < t i) → ∀ i x, ‖(t i • ((Y' + ∑ l, t l • B l)⁻¹ * B i)).mulVec x‖ ≤ W * ‖x‖ := by
  first | exact @GlobalTheory.smul_inv_mul_posSemidef_uniform_bound | exact GlobalTheory.smul_inv_mul_posSemidef_uniform_bound | (intros; apply GlobalTheory.smul_inv_mul_posSemidef_uniform_bound <;> assumption)
end _root_.GlobalTheory.T
