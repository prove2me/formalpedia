-- Prove2me | solution 1 for LongGapsBetweenPrimes.residueWeight_eq_replaced_of_uncovered
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:09:20.081895+00:00
-- url     : https://prove2.me/submissions/0aa557fd-aaa8-44fe-9804-2fc384355a10

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution {P k : ℕ} (D : ℝ)
    (root : (p : PrimeIndex P) → Fin k → Fin p.val) (i : Fin k)
    (t : (p : PrimeIndex P) → Fin p.val) (hi : ∀ p, t p ≠ root p i) :
    residueWeight P k D root t = replacedResidueWeight P k D root i t := by
  have hlocal (p : PrimeIndex P) (j : Option (Fin k)) :
      rawLocalBasis (root p) j (t p) = replacedLocalBasis (root p) i j (t p) := by
    cases j with
    | none => rfl
    | some j =>
        by_cases h : j = i <;>
          simp [rawLocalBasis, replacedLocalBasis, h, residueFactor, hi]
  simp only [residueWeight, replacedResidueWeight, basisWeight, productBasis, hlocal]
end LongGapsBetweenPrimes
