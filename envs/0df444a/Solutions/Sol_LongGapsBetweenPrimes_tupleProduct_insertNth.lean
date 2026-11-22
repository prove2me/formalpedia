-- Prove2me | solution 1 for LongGapsBetweenPrimes.tupleProduct_insertNth
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:05:43.525803+00:00
-- url     : https://prove2.me/submissions/818c9bdd-581c-4e7c-af1c-74f07710c9ec

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution {P k : ℕ} (i : Fin (k + 1)) (d : DivisorIndex P)
    (r : DivisorTuple P k) : tupleProduct (i.insertNth d r) = d.val * tupleProduct r := by
  unfold tupleProduct
  rw [Fin.prod_univ_succAbove _ i]
  simp
end LongGapsBetweenPrimes
