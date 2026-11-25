-- Prove2me | solution 1 for GlobalTheory.StrictUpperNilpotentFlagMeasures.pow_apply_eq_zero_of_strictUpper
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:09:55.813073+00:00
-- url     : https://prove2.me/submissions/f27fddca-0266-49be-a39f-b215e042934b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_PowApplyEqZeroOfStrictUpper

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.StrictUpperNilpotentFlagMeasures
namespace GlobalTheory.StrictUpperNilpotentFlagMeasures
theorem _root_.solution {m : ℕ} {X : Matrix (Fin m) (Fin m) ℂ}
    (hX : ∀ i j : Fin m, (j : ℕ) ≤ (i : ℕ) → X i j = 0) (n : ℕ) :
    ∀ i j : Fin m, (j : ℕ) < (i : ℕ) + n → (X ^ n) i j = 0 := by
  induction n with
  | zero =>
    intro i j h
    rw [pow_zero]
    apply Matrix.one_apply_ne
    rintro rfl
    omega
  | succ n ih =>
    intro i j h
    rw [pow_succ, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hk : (k : ℕ) < (i : ℕ) + n
    · rw [ih i k hk, zero_mul]
    · rw [hX k j (by omega), mul_zero]
end GlobalTheory.StrictUpperNilpotentFlagMeasures
