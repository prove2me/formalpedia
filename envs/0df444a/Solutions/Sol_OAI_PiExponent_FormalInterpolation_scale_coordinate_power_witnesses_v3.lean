-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.scale_coordinate_power_witnesses_v3
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T19:34:22.213428+00:00
-- url     : https://prove2.me/submissions/4cdf462b-6e7a-4946-bb88-c2f4a32fa6e3

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

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
  constructor
  · exact Nat.mul_pos (hn i) hk
  · have hpow : (MvPolynomial.X i ^ n i) ^ k ∈ (I ^ s) ^ k :=
      Ideal.pow_mem_pow (hmem i) k
    simpa only [← pow_mul] using hpow