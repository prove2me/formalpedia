-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.withTopInt_nonneg_finite_nat
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T19:40:22.086867+00:00
-- url     : https://prove2.me/submissions/8d299105-6add-4436-bf37-e4adb9c8606b

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Mathlib
open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

theorem solution
    (v : WithTop Int) (hne : v ≠ ⊤) (hnonneg : 0 ≤ v) :
    ∃ k : Nat, v = ((k : Int) : WithTop Int) := by
  obtain ⟨j, rfl⟩ := WithTop.ne_top_iff_exists.mp hne
  have : (0:ℤ) ≤ j := by exact_mod_cast hnonneg
  exact ⟨j.toNat, by rw [Int.toNat_of_nonneg this]⟩
