-- Prove2me | solution 1 for LongGapsBetweenPrimes.tupleRegion_card_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:07:11.30182+00:00
-- url     : https://prove2.me/submissions/f2e8d99c-5e56-41d8-b30c-20baa4d523bd

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
import Theorems.Thm_LongGapsBetweenPrimes_tupleAssignment_injective
import Theorems.Thm_LongGapsBetweenPrimes_assignmentProduct_tupleAssignment
import Theorems.Thm_LongGapsBetweenPrimes_card_assignment_family_le

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution {P k : ℕ} (hP : Squarefree P) {D : ℝ} (hD : 1 ≤ D)
    (root : (p : PrimeIndex P) → Fin k → Fin p.val) (hroot : ∀ p, Function.Injective (root p)) :
    (Fintype.card (tupleRegion P k D) : ℝ) ≤ 4 * D ^ 2 := by
  apply card_assignment_family_le root hroot
    (fun r : tupleRegion P k D => tupleAssignment r.val) (tupleAssignment_injective hP D) hD
  intro r
  rw [assignmentProduct_tupleAssignment hP r.val (Finset.mem_filter.mp r.property).2.1]
  exact (Finset.mem_filter.mp r.property).2.2
end LongGapsBetweenPrimes
