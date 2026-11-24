-- Prove2me | solution 1 for GlobalTheory.TangentRigid.exists_param
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:10:29.200015+00:00
-- url     : https://prove2.me/submissions/a8d57f8c-92b0-418d-8949-652f2186a118

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_FirstOrderRigid

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory GlobalTheory.TangentRigid
namespace GlobalTheory.TangentRigid
theorem _root_.solution {k : Type} [Field k] (A B a dA dB : k) (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0)
    (ha : a ≠ 0) (hD : 4 * A ^ 3 + 27 * B ^ 2 ≠ 0) (hd : 12 * A ^ 2 * dA + 54 * B * dB = 0) :
    ∃ w : k, dA = 9 * B * a ^ 2 * w ∧ dB = -2 * A ^ 2 * a ^ 2 * w := by
  have h6 : (6 : k) ≠ 0 := by
    have : (6 : k) = 2 * 3 := by norm_num
    rw [this]; exact mul_ne_zero h2 h3
  have hd' : 2 * A ^ 2 * dA + 9 * B * dB = 0 := by
    apply mul_left_cancel₀ h6
    linear_combination hd
  refine ⟨(3 * B * dA - 2 * A * dB) / ((4 * A ^ 3 + 27 * B ^ 2) * a ^ 2), ?_, ?_⟩
  · rw [← mul_div_assoc, eq_div_iff (mul_ne_zero hD (pow_ne_zero 2 ha))]
    linear_combination (2 * A * a ^ 2) * hd'
  · rw [← mul_div_assoc, eq_div_iff (mul_ne_zero hD (pow_ne_zero 2 ha))]
    linear_combination (3 * B * a ^ 2) * hd'
end GlobalTheory.TangentRigid
