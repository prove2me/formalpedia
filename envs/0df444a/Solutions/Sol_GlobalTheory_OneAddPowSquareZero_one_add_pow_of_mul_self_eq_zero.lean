-- Prove2me | solution 1 for GlobalTheory.OneAddPowSquareZero.one_add_pow_of_mul_self_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:16:19.916344+00:00
-- url     : https://prove2.me/submissions/d8215857-85f1-4ca8-b6aa-4788667ea7de

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OneAddPowOfMulSelfEqZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.OneAddPowSquareZero
namespace GlobalTheory.OneAddPowSquareZero
theorem _root_.solution :
    ∀ {S : Type} [inst : Ring S] (X : S), X * X = (0 : S) →
      ∀ (N : ℕ), ((1 : S) + X) ^ N = (1 : S) + (↑N : S) * X := by
  intro S _ X hX N
  induction N with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih, Nat.cast_succ, mul_add, mul_one, add_mul, one_mul, mul_assoc, hX,
      mul_zero, add_zero, add_mul, one_mul, add_assoc]
end GlobalTheory.OneAddPowSquareZero
