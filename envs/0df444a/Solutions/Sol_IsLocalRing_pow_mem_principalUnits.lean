-- Prove2me | solution 1 for IsLocalRing.pow_mem_principalUnits
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/d553af95-947c-54f8-a564-d67efedae0b1

import Mathlib
import Definitions.Def_LocalRing_PrincipalUnits
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsLocalRing_pow_mem_principalUnits

set_option autoImplicit false
open IsLocalRing

open IsLocalRing in
theorem solution {R : Type*} [CommRing R] [IsLocalRing R]
    {p : ℕ} (hp : p.Prime) {e : ℕ} (hpe : (p : R) ∈ maximalIdeal R ^ e)
    {k : ℕ} {u : Rˣ} (hu : u ∈ principalUnits R k) :
    u ^ p ∈ principalUnits R (min (p * k) (k + e)) := by
  set N := min (p * k) (k + e) with hN
  set x : R := (u : R) - 1 with hx_def
  have hx : x ∈ maximalIdeal R ^ k := hu
  have hxj : ∀ j : ℕ, x ^ j ∈ maximalIdeal R ^ (k * j) := fun j => by
    rw [pow_mul]; exact Ideal.pow_mem_pow hx j
  rw [mem_principalUnits_iff, Units.val_pow_eq_pow_val]

  have hexp : (u : R) ^ p - 1 = ∑ j ∈ Finset.range p, x ^ (j + 1) * (p.choose (j + 1) : R) := by
    have hu1 : (u : R) = x + 1 := by rw [hx_def]; ring
    rw [hu1, add_pow, Finset.sum_range_succ']
    simp only [one_pow, mul_one, pow_zero, Nat.choose_zero_right, Nat.cast_one, add_sub_cancel_right]
  rw [hexp]
  refine Ideal.sum_mem _ fun j hj => ?_
  have hjp : j + 1 ≤ p := Finset.mem_range.mp hj
  rcases lt_or_eq_of_le hjp with hlt | heq
  ·
    obtain ⟨m, hm⟩ := hp.dvd_choose_self (Nat.succ_ne_zero j) hlt
    have hxk : x ^ (j + 1) ∈ maximalIdeal R ^ k :=
      Ideal.pow_le_pow_right (Nat.le_mul_of_pos_right k (Nat.succ_pos j)) (hxj (j + 1))
    have h1 : x ^ (j + 1) * (p.choose (j + 1) : R) ∈ maximalIdeal R ^ (k + e) := by
      rw [pow_add, hm, Nat.cast_mul, ← mul_assoc]
      exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_mul hxk hpe)
    exact Ideal.pow_le_pow_right (min_le_right _ _) h1
  ·
    rw [heq, Nat.choose_self, Nat.cast_one, mul_one]
    exact Ideal.pow_le_pow_right ((min_le_left _ _).trans_eq (mul_comm p k)) (hxj p)

end S_IsLocalRing_pow_mem_principalUnits
end P2MW
export P2MW.S_IsLocalRing_pow_mem_principalUnits (solution)
