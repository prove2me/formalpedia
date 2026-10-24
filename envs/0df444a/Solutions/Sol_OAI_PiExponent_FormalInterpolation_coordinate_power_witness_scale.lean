-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.coordinate_power_witness_scale
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T19:51:08.447005+00:00
-- url     : https://prove2.me/submissions/646941e5-da10-40b0-8a4c-67db8ba2e7ba

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

open OAI.PiExponent.FormalInterpolation

theorem solution {R : Type} [CommSemiring R] (I : Ideal R) (x : R) (w c : Real) (s n k : Nat)
    (hs : 0 < s) (hn : 0 < n) (hk : 0 < k) (hmem : x ^ n ∈ I ^ s)
    (hbound : (n : Real) * w < (s : Real) * c) :
    0 < n * k ∧ x ^ (n * k) ∈ I ^ (s * k) ∧ (n * k : Real) * w < (s * k : Real) * c := by
  refine ⟨Nat.mul_pos hn hk, ?_, ?_⟩
  · simpa [← pow_mul] using (Ideal.pow_mem_pow hmem k)
  · have hkR : 0 < (k : Real) := by exact_mod_cast hk
    calc
      (n * k : Real) * w = ((n : Real) * w) * (k : Real) := by push_cast; ring
      _ < ((s : Real) * c) * (k : Real) := mul_lt_mul_of_pos_right hbound hkR
      _ = (s * k : Real) * c := by push_cast; ring