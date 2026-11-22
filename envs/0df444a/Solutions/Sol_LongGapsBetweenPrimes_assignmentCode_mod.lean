-- Prove2me | solution 1 for LongGapsBetweenPrimes.assignmentCode_mod
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:03:06.642884+00:00
-- url     : https://prove2.me/submissions/63b54ce9-d795-4aaa-847f-de1b2f10635d

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution {P k : ℕ} (root : (p : PrimeIndex P) → Fin k → Fin p.val)
    (σ : PrimeIndex P → Option (Fin k)) (p : PrimeIndex P) (hp : (σ p).isSome) :
    assignmentCode root σ % p.val = (assignedRoot root σ p).val :=
  (Classical.choose_spec (exists_assignment_residue root σ)).2 p hp
end LongGapsBetweenPrimes
