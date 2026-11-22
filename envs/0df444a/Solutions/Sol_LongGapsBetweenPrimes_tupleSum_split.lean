-- Prove2me | solution 1 for LongGapsBetweenPrimes.tupleSum_split
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:09:01.807453+00:00
-- url     : https://prove2.me/submissions/9d0cf110-6007-48bb-87b4-23dc24df0315

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
import Theorems.Thm_LongGapsBetweenPrimes_tupleRegion_insertNth

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution {P k : ℕ} (i : Fin (k + 1)) (D : ℝ)
    (G : Fin (k + 1) → DivisorIndex P → ℝ) :
    (∑ r ∈ tupleRegion P (k + 1) D, ∏ j, G j (r j)) =
      ∑ r ∈ tupleRegion P k D,
        (∑ d : DivisorIndex P,
          if (d.val : ℝ) ≤ D / tupleProduct r ∧ d.val.Coprime (tupleProduct r) then G i d else 0) *
          ∏ j, G (i.succAbove j) (r j) := by
  classical
  let f (r : DivisorTuple P (k + 1)) : ℝ :=
    if r ∈ tupleRegion P (k + 1) D then ∏ j, G j (r j) else 0
  have h := Fintype.sum_equiv (Fin.insertNthEquiv (fun _ => DivisorIndex P) i)
    (fun dr => f (i.insertNth dr.1 dr.2)) f (fun _ => rfl)
  rw [Fintype.sum_prod_type, Finset.sum_comm] at h
  simpa [f, tupleRegion_insertNth, Fin.prod_univ_succAbove _ i,
    ite_and, Finset.sum_mul, ite_mul] using h.symm
end LongGapsBetweenPrimes
