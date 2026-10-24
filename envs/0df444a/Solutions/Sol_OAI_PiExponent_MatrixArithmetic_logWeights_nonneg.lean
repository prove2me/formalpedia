-- Prove2me | solution 1 for OAI.PiExponent.MatrixArithmetic.logWeights_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-24T04:51:28.197301+00:00
-- url     : https://prove2.me/submissions/1ff6292e-ed51-40f1-886c-16fb2dc67ee8

import Definitions.Def_PiExponent_FiniteMinorComparison

open OAI.PiExponent
open scoped BigOperators

theorem solution
    {m : ℕ} (q : Fin m → ℕ) (hq : ∀ i, 2 ≤ q i) :
    ∀ i, 0 ≤ OAI.PiExponent.MatrixArithmetic.logWeights q i := by
  intro i
  change 0 ≤ (⌈Real.log (q i)⌉₊ : ℝ)
  exact_mod_cast (Nat.zero_le (⌈Real.log (q i)⌉₊))