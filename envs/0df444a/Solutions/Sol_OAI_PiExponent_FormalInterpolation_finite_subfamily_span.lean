-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.finite_subfamily_span
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T08:38:14.670298+00:00
-- url     : https://prove2.me/submissions/fdd35ddf-56dc-4fd6-af4f-d05598f4051a

import Mathlib.RingTheory.Ideal.Operations
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_mem_ideal_span_range_finite_support
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_finite_set_memberships_to_fin_subfamily

open Set

theorem solution
    {R : Type} [CommSemiring R] {α ι : Type} [Fintype α]
    (x : α → R) (g : ι → R)
    (hx : ∀ a, x a ∈ Ideal.span (Set.range g)) :
    ∃ n : Nat, ∃ f : Fin n → ι,
      ∀ a, x a ∈ Ideal.span (Set.range (fun j => g (f j))) := by
  apply OAI.PiExponent.FormalInterpolation.finite_set_memberships_to_fin_subfamily
    (x := x) (g := g)
  intro a
  exact OAI.PiExponent.FormalInterpolation.mem_ideal_span_range_finite_support
    (g := g) (x := x a) (hx a)