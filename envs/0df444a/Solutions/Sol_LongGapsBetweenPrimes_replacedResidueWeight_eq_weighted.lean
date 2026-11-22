-- Prove2me | solution 1 for LongGapsBetweenPrimes.replacedResidueWeight_eq_weighted
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:13:06.532739+00:00
-- url     : https://prove2.me/submissions/928119af-737f-43a7-a2f4-ef14e422c57a

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
import Theorems.Thm_LongGapsBetweenPrimes_replacedResidueWeight_split
import Theorems.Thm_LongGapsBetweenPrimes_weightedResidueWeight_eq_sum

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution {P k : ℕ} (hP : Squarefree P) (D : ℝ)
    (root : (p : PrimeIndex P) → Fin (k + 1) → Fin p.val) (i : Fin (k + 1))
    (t : (p : PrimeIndex P) → Fin p.val) :
    replacedResidueWeight P (k + 1) D root i t =
      weightedResidueWeight P k D (fun p j => root p (i.succAbove j))
        (fun r => coefficientRemainder P (tupleProduct r) D) t := by
  rw [replacedResidueWeight_split hP, weightedResidueWeight_eq_sum]
end LongGapsBetweenPrimes
