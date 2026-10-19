-- Prove2me | solution 1 for OAI.CirculantHadamard.CyclotomicRings.prime_not_dvd_awayOrder
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T09:49:59.337912+00:00
-- url     : https://prove2.me/submissions/c13e7c58-734a-43f3-97af-901c59ab751f

import Mathlib
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclotomicRings

open OAI OAI.CirculantHadamard OAI.CirculantHadamard.CyclotomicRings

theorem solution (u p : ℕ) (hu : Odd u) (hp : p ∈ u.primeFactors) :
    ¬p ∣ awayOrder u p := by
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hpu : p ∣ u := Nat.dvd_of_mem_primeFactors hp
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.2 hu) (even_iff_two_dvd.2 hpu)
  unfold awayOrder orderOfSet
  intro h
  rcases (Nat.Prime.dvd_mul hpp).1 h with h4 | hprod
  · have : p ∣ 2 ^ 2 := by norm_num; exact h4
    have := hpp.dvd_of_dvd_pow this
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).1 this)
  · obtain ⟨q, hq, hdq⟩ := (Prime.dvd_finset_prod_iff hpp.prime _).1 hprod
    have hqp : q ≠ p := Finset.ne_of_mem_erase hq
    have hq' : q.Prime := Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase hq)
    exact hqp ((Nat.prime_dvd_prime_iff_eq hpp hq').1 hdq).symm
