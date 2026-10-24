-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.ideal_span_pow_le_span_generator_products
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T05:53:49.977402+00:00
-- url     : https://prove2.me/submissions/9c7b09a5-0205-49dd-95bb-c8281aead8d1

import Mathlib
open scoped BigOperators

theorem solution {A R : Type} [CommSemiring R] (g : A → R) (m : Nat) : (Ideal.span (Set.range g)) ^ m ≤ Ideal.span (Set.range (fun u : Fin m → A => ∏ i, g (u i))) := by
  induction m with
  | zero => simp
  | succ n ih =>
    rw [pow_succ]
    refine (Ideal.mul_mono_left ih).trans ?_
    rw [Ideal.span_mul_span']
    apply Ideal.span_mono
    rintro x ⟨a, ⟨u, rfl⟩, b, ⟨c, rfl⟩, rfl⟩
    refine ⟨Fin.snoc u c, ?_⟩
    simp [Fin.prod_univ_castSucc]
