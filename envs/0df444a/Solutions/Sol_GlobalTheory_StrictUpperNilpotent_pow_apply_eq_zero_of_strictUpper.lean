-- Prove2me | solution 1 for GlobalTheory.StrictUpperNilpotent.pow_apply_eq_zero_of_strictUpper
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:58:49.332441+00:00
-- url     : https://prove2.me/submissions/ddc27641-d84d-4fda-be4c-866ce2973c80

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PowApplyEqZeroOfStrictUpper

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.StrictUpperNilpotent
namespace GlobalTheory.StrictUpperNilpotent
theorem _root_.solution {L : Type} [inst : Field L] {n : ℕ}
    {y : Matrix (Fin n) (Fin n) L} (hy : ∀ (i j : Fin n), j ≤ i → y i j = (0 : L)) :
    ∀ (k : ℕ) (i j : Fin n), (↑j : ℕ) < (↑i : ℕ) + k → (y ^ k) i j = (0 : L) := by
  intro k
  induction k with
  | zero =>
    intro i j h
    have hne : i ≠ j := by
      rintro rfl
      simp at h
    rw [pow_zero, Matrix.one_apply_ne hne]
  | succ k ih =>
    intro i j h
    rw [pow_succ, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    by_cases hl : (l : ℕ) < (i : ℕ) + k
    · rw [ih i l hl, zero_mul]
    · have hjl : j ≤ l := by
        rw [Fin.le_def]
        omega
      rw [hy l j hjl, mul_zero]
end GlobalTheory.StrictUpperNilpotent
