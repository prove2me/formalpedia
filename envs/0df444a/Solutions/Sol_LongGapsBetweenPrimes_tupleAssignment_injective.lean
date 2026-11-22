-- Prove2me | solution 1 for LongGapsBetweenPrimes.tupleAssignment_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:01:58.24521+00:00
-- url     : https://prove2.me/submissions/dc6870e9-a18d-4536-9e63-cc9ee646a184

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
import Theorems.Thm_LongGapsBetweenPrimes_tupleAssignment_eq_some

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution {P k : ℕ} (hP : Squarefree P) (D : ℝ) :
    Function.Injective (fun r : tupleRegion P k D => tupleAssignment r.val) := by
  classical
  intro r s hrs
  dsimp only at hrs
  apply Subtype.ext
  funext i
  apply Subtype.ext
  apply (Nat.Squarefree.ext_iff
    (hP.squarefree_of_dvd (Nat.dvd_of_mem_divisors (r.val i).property))
    (hP.squarefree_of_dvd (Nat.dvd_of_mem_divisors (s.val i).property))).mpr
  intro p hp
  by_cases hpP : p ∣ P
  · let p' : PrimeIndex P := ⟨p, hp.mem_primeFactors hpP hP.ne_zero⟩
    rw [← tupleAssignment_eq_some r.val (Finset.mem_filter.mp r.property).2.1 p' i,
      ← tupleAssignment_eq_some s.val (Finset.mem_filter.mp s.property).2.1 p' i, hrs]
  · constructor <;> intro h
    · exact (hpP (h.trans (Nat.dvd_of_mem_divisors (r.val i).property))).elim
    · exact (hpP (h.trans (Nat.dvd_of_mem_divisors (s.val i).property))).elim
end LongGapsBetweenPrimes
