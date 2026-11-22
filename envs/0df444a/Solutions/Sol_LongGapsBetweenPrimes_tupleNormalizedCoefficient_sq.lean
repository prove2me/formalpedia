-- Prove2me | solution 1 for LongGapsBetweenPrimes.tupleNormalizedCoefficient_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:04:43.887802+00:00
-- url     : https://prove2.me/submissions/4812b1b4-5d33-47dc-bde7-78ab69783dba

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
import Theorems.Thm_LongGapsBetweenPrimes_assignmentNormalizer_sq
import Theorems.Thm_LongGapsBetweenPrimes_assignmentVariance_tuple

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution {P k : ℕ} (hP : Squarefree P) (r : DivisorTuple P k)
    (hpair : ∀ i j, i ≠ j → Nat.Coprime (r i).val (r j).val) :
    tupleNormalizedCoefficient r ^ 2 = tupleMass r := by
  rw [tupleNormalizedCoefficient, mul_pow,
    assignmentNormalizer_sq _ (fun p => (Nat.prime_of_mem_primeFactors p.property).one_lt),
    assignmentVariance_tuple hP r hpair]
  simp only [tupleAmplitude, tupleMass, ← Finset.prod_pow,
    ← Finset.prod_mul_distrib, mul_one_div]
end LongGapsBetweenPrimes
