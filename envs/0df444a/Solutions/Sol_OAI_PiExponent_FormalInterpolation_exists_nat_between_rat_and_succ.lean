-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.exists_nat_between_rat_and_succ
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-24T04:21:48.365006+00:00
-- url     : https://prove2.me/submissions/28bfbb9c-a6a8-48b9-8658-bebbece621e0

import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Floor

theorem solution (q : Rat) (hq : 0 < q) :
    ∃ B : Nat, (q : Real) ≤ (B : Real) ∧ (B : Real) < (q : Real) + 1 := by
  let b : Int := ⌈q⌉
  have hb : 0 ≤ b := by
    exact Int.ceil_nonneg (le_of_lt hq)
  have hB : (b.toNat : Rat) = b := by
    exact_mod_cast Int.toNat_of_nonneg hb
  have hB' : (b.toNat : Real) = (b : Real) := by
    exact_mod_cast hB
  refine ⟨b.toNat, ?_, ?_⟩
  · rw [hB']
    exact_mod_cast (show q ≤ b by
      dsimp [b]
      exact Int.le_ceil q)
  · rw [hB']
    exact_mod_cast (show b < q + 1 by
      dsimp [b]
      exact Int.ceil_lt_add_one q)
