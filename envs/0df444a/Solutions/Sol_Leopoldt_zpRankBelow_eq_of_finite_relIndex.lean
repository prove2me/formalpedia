-- Prove2me | solution 1 for Leopoldt.zpRankBelow_eq_of_finite_relIndex
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-09-27T23:10:05.230257+00:00
-- url     : https://prove2.me/submissions/87aa00b7-f1c5-4f6c-ad9f-541bd465c893

import Definitions.Def_LeopoldtDefect
import Theorems.Thm_Leopoldt_zpRankBelow_eq_of_power_mem

open Leopoldt

theorem solution (p : ℕ) [Fact p.Prime]
    {G : Type*} [CommGroup G] [TopologicalSpace G]
    (b : ℕ) {H H' : Subgroup G} (hsub : H' ≤ H)
    [H'.IsFiniteRelIndex H] :
    zpRankBelow p b H' = zpRankBelow p b H := by
  apply zpRankBelow_eq_of_power_mem p b hsub
    (Nat.factorial (H'.relIndex H)) (Nat.factorial_ne_zero _)
  intro x hx
  have h := Subgroup.pow_mem_of_relIndex_ne_zero_of_dvd
    (H := H') (K := H) (Subgroup.relIndex_ne_zero) hx
    (fun m hm hle => Nat.dvd_factorial hm hle)
  exact h.1
