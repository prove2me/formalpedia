-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.weighted_component_span_pow_span_power
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-24T04:46:12.260988+00:00
-- url     : https://prove2.me/submissions/5dac27ca-f685-45fd-9ee1-9dc447c9dcfb

import Mathlib.RingTheory.Ideal.Operations
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_ideal_span_pow_le_span_generator_products
open scoped BigOperators

theorem solution {A R : Type} [CommSemiring R] (g : A → R) (m : Nat)
    {T : Set R} {x : R} (hx : x ∈ Ideal.span (Set.range g))
    (hprod : ∀ u : Fin m → A, (∏ i, g (u i)) ∈ Ideal.span T) :
    x ^ m ∈ Ideal.span T := by
  have hproducts :
      Ideal.span (Set.range (fun u : Fin m → A => ∏ i, g (u i))) ≤ Ideal.span T := by
    apply Ideal.span_le.mpr
    rintro z ⟨u, rfl⟩
    exact hprod u
  exact ((OAI.PiExponent.FormalInterpolation.ideal_span_pow_le_span_generator_products g m).trans hproducts)
    (Ideal.pow_mem_pow hx m)