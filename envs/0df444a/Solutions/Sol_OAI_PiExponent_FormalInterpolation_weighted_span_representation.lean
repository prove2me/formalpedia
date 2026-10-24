-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.weighted_span_representation
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T08:22:29.754276+00:00
-- url     : https://prove2.me/submissions/591bb86e-71ad-4909-8adb-20d4518f7242

import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

open scoped BigOperators

theorem solution
    {d k : Nat} (g : Fin k → MvPolynomial (Fin d) Complex)
    (J : Ideal (MvPolynomial (Fin d) Complex))
    (hspan : Ideal.span (Set.range g) = J)
    (f : MvPolynomial (Fin d) Complex)
    (hmem : f ∈ J) :
    ∃ a : Fin k → MvPolynomial (Fin d) Complex,
      f = ∑ j : Fin k, a j * g j := by
  classical
  rw [← hspan] at hmem
  induction hmem using Submodule.span_induction with
  | mem x hx =>
      rcases hx with ⟨j, rfl⟩
      refine ⟨fun i => if i = j then 1 else 0, ?_⟩
      have hsum :
          ∑ i : Fin k, (if i = j then 1 else 0) * g i =
            (if j = j then 1 else 0) * g j := by
        apply Finset.sum_eq_single j
        · intro b hb hbj
          simp [hbj]
        · intro hj
          exact (hj (Finset.mem_univ _)).elim
      simpa using hsum
  | zero =>
      exact ⟨0, by simp⟩
  | add x y hx hy ihx ihy =>
      rcases ihx with ⟨a, ha⟩
      rcases ihy with ⟨b, hb⟩
      refine ⟨a + b, ?_⟩
      rw [ha, hb]
      simp [Finset.sum_add_distrib, add_mul]
  | smul r x hx ih =>
      rcases ih with ⟨a, ha⟩
      refine ⟨fun j => r * a j, ?_⟩
      rw [smul_eq_mul, ha]
      simp [Finset.mul_sum, mul_assoc]