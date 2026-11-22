-- Prove2me | solution 1 for LongGapsBetweenPrimes.assignmentCode_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:03:06.220801+00:00
-- url     : https://prove2.me/submissions/a2d98cf1-bbc4-4906-b1bb-106b63a0a05a

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution {P k : ℕ} (root : (p : PrimeIndex P) → Fin k → Fin p.val)
    (σ : PrimeIndex P → Option (Fin k)) :
    assignmentCode root σ < assignmentProduct (fun p : PrimeIndex P => p.val) σ :=
  (Classical.choose_spec (exists_assignment_residue root σ)).1
end LongGapsBetweenPrimes
