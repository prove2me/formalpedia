-- Prove2me | solution 1 for GlobalTheory.CommutatorPowerFormula.commutator_pow_of_commutator_eq_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:31:43.069585+00:00
-- url     : https://prove2.me/submissions/55491ea9-00af-42d4-9473-a3876767d488

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CommutatorPowOfCommutatorEqSmul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CommutatorPowerFormula
namespace GlobalTheory.CommutatorPowerFormula
theorem _root_.solution {A : Type} [Ring A] [Algebra ℚ A] {H X : A} {s : ℚ}
    (h : H * X - X * H = s • X) (k : ℕ) :
    H * X ^ k - X ^ k * H = ((k : ℚ) * s) • X ^ k := by
  induction k with
  | zero => simp
  | succ n ih =>
    have e : H * X ^ (n + 1) - X ^ (n + 1) * H
        = (H * X ^ n - X ^ n * H) * X + X ^ n * (H * X - X * H) := by
      rw [pow_succ]
      noncomm_ring
    rw [e, ih, h, smul_mul_assoc, mul_smul_comm, ← pow_succ, ← add_smul]
    congr 1
    push_cast
    ring
end GlobalTheory.CommutatorPowerFormula
