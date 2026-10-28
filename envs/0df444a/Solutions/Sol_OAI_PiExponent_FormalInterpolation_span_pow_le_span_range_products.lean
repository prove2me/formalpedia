-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.span_pow_le_span_range_products
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T18:51:34.822994+00:00
-- url     : https://prove2.me/submissions/0b75ff4b-6fa1-433e-9756-9538ba928a4a

import Mathlib

theorem solution
    {d n k : Nat} (g : Fin n → MvPolynomial (Fin d) Complex) :
    (Ideal.span (Set.range g)) ^ k ≤
      Ideal.span (Set.range fun f : Fin k → Fin n => ∏ t : Fin k, g (f t)) := by
  rw [Ideal.span, Submodule.span_pow]
  refine Submodule.span_le.mpr fun y hy => ?_
  rw [Set.mem_pow] at hy
  obtain ⟨φ, rfl⟩ := hy
  have hc : ∀ t, ∃ m, g m = (φ t : MvPolynomial (Fin d) Complex) := fun t => (φ t).2
  choose ψ hψ using hc
  refine Ideal.subset_span ⟨ψ, ?_⟩
  rw [List.prod_ofFn]
  exact Finset.prod_congr rfl fun t _ => hψ t
