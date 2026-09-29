-- Prove2me | solution 1 for IntermediateField.not_mem_adjoin_pow_of_transcendental
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/175a4d8a-b5d9-58bc-ba04-355e8e0c39c0

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IntermediateField_not_mem_adjoin_pow_of_transcendental

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

set_option autoImplicit false

universe u v

open Polynomial

theorem solution
    (K : Type u) [Field K] (L : Type v) [Field L] [Algebra K L] (y : L) (hy : Transcendental K y)
    (n : ℕ) (hn : 2 ≤ n) :
    y ∉ IntermediateField.adjoin K ({y ^ n} : Set L) := by
  intro hmem
  rw [IntermediateField.mem_adjoin_simple_iff] at hmem
  obtain ⟨P, Q, hPQ⟩ := hmem
  have hn0 : 0 < n := by omega
  by_cases hQ : aeval (y ^ n) Q = 0
  · rw [hQ, div_zero] at hPQ
    exact hy (hPQ ▸ isAlgebraic_zero)
  have hQ0 : Q ≠ 0 := fun h0 => hQ (by rw [h0, map_zero])

  have hmul : y * aeval (y ^ n) Q = aeval (y ^ n) P := (eq_div_iff hQ).mp hPQ
  have hR : aeval y (X * expand K n Q - expand K n P) = 0 := by
    rw [map_sub, map_mul, aeval_X, expand_aeval, expand_aeval, hmul, sub_self]

  have hR0 : (X * expand K n Q - expand K n P : K[X]) ≠ 0 := by
    intro h
    have hc := congrArg (fun R : K[X] => R.coeff (n * Q.natDegree + 1)) h
    have hndvd : ¬ n ∣ n * Q.natDegree + 1 := fun hd => by
      have h1 : n ∣ 1 := (Nat.dvd_add_right (dvd_mul_right n Q.natDegree)).mp hd
      have : n ≤ 1 := Nat.le_of_dvd one_pos h1
      omega
    simp only [coeff_sub, coeff_zero, coeff_X_mul, coeff_expand hn0, dvd_mul_right, if_true, hndvd, if_false,
      sub_zero, Nat.mul_div_cancel_left _ hn0] at hc
    exact hQ0 (leadingCoeff_eq_zero.mp hc)
  exact hy ⟨_, hR0, hR⟩

end S_IntermediateField_not_mem_adjoin_pow_of_transcendental
end P2MW
export P2MW.S_IntermediateField_not_mem_adjoin_pow_of_transcendental (solution)
