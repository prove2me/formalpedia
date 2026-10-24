-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.scale_coordinate_power_witnesses
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T19:43:05.806983+00:00
-- url     : https://prove2.me/submissions/0eb879bb-cb56-4710-9a06-148863c69527

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Mathlib
open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

theorem solution
    {d : Nat} (I : Ideal (MvPolynomial (Fin d) Complex))
    (s : Nat) (n : Fin d → Nat)
    (hn : ∀ i, 0 < n i)
    (hmem : ∀ i, MvPolynomial.X i ^ n i ∈ I ^ s)
    (k : Nat) (hk : 0 < k) :
    ∀ i : Fin d, 0 < n i * k ∧
      MvPolynomial.X i ^ (n i * k) ∈ I ^ (s * k) := by
  intro i
  refine ⟨Nat.mul_pos (hn i) hk, ?_⟩
  rw [pow_mul, pow_mul]
  exact Ideal.pow_mem_pow (hmem i) k
