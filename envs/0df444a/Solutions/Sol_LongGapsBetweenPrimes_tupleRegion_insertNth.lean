-- Prove2me | solution 1 for LongGapsBetweenPrimes.tupleRegion_insertNth
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:07:32.7558+00:00
-- url     : https://prove2.me/submissions/af4b0c64-6289-48e4-ac99-13d257ff732f

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
import Theorems.Thm_LongGapsBetweenPrimes_tupleProduct_pos
import Theorems.Thm_LongGapsBetweenPrimes_tupleProduct_insertNth
import Theorems.Thm_LongGapsBetweenPrimes_tuplePairwise_insertNth

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution {P k : ℕ} (i : Fin (k + 1)) (d : DivisorIndex P)
    (r : DivisorTuple P k) (D : ℝ) :
    i.insertNth d r ∈ tupleRegion P (k + 1) D ↔
      r ∈ tupleRegion P k D ∧ (d.val : ℝ) ≤ D / tupleProduct r ∧
        d.val.Coprime (tupleProduct r) := by
  classical
  have hr : 0 < (tupleProduct r : ℝ) := by exact_mod_cast tupleProduct_pos r
  have hd : (1 : ℝ) ≤ d.val := by exact_mod_cast Nat.pos_of_mem_divisors d.property
  simp only [tupleRegion, Finset.mem_filter, Finset.mem_univ, true_and,
    tuplePairwise_insertNth, tupleProduct_insertNth, Nat.cast_mul, le_div_iff₀ hr]
  constructor
  · rintro ⟨⟨hpair, hcop⟩, hD⟩
    exact ⟨⟨hpair, (le_mul_of_one_le_left hr.le hd).trans hD⟩, hD, hcop⟩
  · rintro ⟨⟨hpair, _⟩, hD, hcop⟩
    exact ⟨⟨hpair, hcop⟩, hD⟩
end LongGapsBetweenPrimes
