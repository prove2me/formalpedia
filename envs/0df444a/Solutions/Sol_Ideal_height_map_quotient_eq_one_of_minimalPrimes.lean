-- Prove2me | solution 1 for Ideal.height_map_quotient_eq_one_of_minimalPrimes
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-27T00:57:26.762969+00:00
-- url     : https://prove2.me/submissions/5b3992ab-2a3c-4b50-919d-61169303a22b

import Mathlib.RingTheory.Ideal.KrullsHeightTheorem


set_option autoImplicit false

/-- In a Noetherian ring, a component of a principal cut of a prime has
relative height exactly one, provided the equation is outside that prime. -/
theorem Ideal.height_map_quotient_eq_one_of_minimalPrimes
    {R : Type*} [CommRing R] [IsNoetherianRing R]
    (p q : Ideal R) (hp : p.IsPrime) (x : R) (hx : x ∉ p)
    (hq : q ∈ (p ⊔ Ideal.span {x}).minimalPrimes) :
    (q.map (Ideal.Quotient.mk p)).height = 1 := by
  let : p.IsPrime := hp
  apply le_antisymm (Ideal.map_height_le_one_of_mem_minimalPrimes hq)
  rw [Order.one_le_iff_ne_zero, Ne, Ideal.height_eq_zero_iff_eq_bot]
  intro heq
  have hspan : Ideal.span {x} ≤ q := le_sup_right.trans hq.le
  have hxq : x ∈ q := hspan (Ideal.subset_span (Set.mem_singleton x))
  have hmem := Ideal.mem_map_of_mem (Ideal.Quotient.mk p) hxq
  rw [heq, Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem] at hmem
  exact hx hmem

theorem solution
{R : Type*} [CommRing R] [IsNoetherianRing R]
    (p q : Ideal R) (hp : p.IsPrime) (x : R) (hx : x ∉ p)
    (hq : q ∈ (p ⊔ Ideal.span {x}).minimalPrimes) :
    (q.map (Ideal.Quotient.mk p)).height = 1 := by
  exact Ideal.height_map_quotient_eq_one_of_minimalPrimes p q hp x hx hq
