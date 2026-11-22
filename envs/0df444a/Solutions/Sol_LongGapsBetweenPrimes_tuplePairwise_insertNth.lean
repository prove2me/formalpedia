-- Prove2me | solution 1 for LongGapsBetweenPrimes.tuplePairwise_insertNth
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:06:15.143629+00:00
-- url     : https://prove2.me/submissions/bf886611-eec4-4cae-824f-62ca20114a4a

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution {P k : ℕ} (i : Fin (k + 1)) (d : DivisorIndex P)
    (r : DivisorTuple P k) :
    (∀ j l, j ≠ l →
      Nat.Coprime (i.insertNth (α := fun _ => DivisorIndex P) d r j).val
        (i.insertNth (α := fun _ => DivisorIndex P) d r l).val) ↔
      (∀ j l, j ≠ l → Nat.Coprime (r j).val (r l).val) ∧ d.val.Coprime (tupleProduct r) := by
  simp [Fin.forall_iff_succAbove i, tupleProduct, Nat.coprime_prod_right_iff,
    Nat.coprime_comm, forall_and, and_comm]
end LongGapsBetweenPrimes
