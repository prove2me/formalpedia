-- Prove2me | solution 1 for LongGapsBetweenPrimes.assignmentPrimes_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:42:32.208335+00:00
-- url     : https://prove2.me/submissions/7e1691ab-d874-4b76-9d6d-5a48aef6bf89

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution {P k : ℕ} (σ : PrimeIndex P → Option (Fin k)) :
    assignmentPrimes σ ⊆ P.primeFactors := by
  intro p hp
  obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp hp
  exact q.property
end LongGapsBetweenPrimes
