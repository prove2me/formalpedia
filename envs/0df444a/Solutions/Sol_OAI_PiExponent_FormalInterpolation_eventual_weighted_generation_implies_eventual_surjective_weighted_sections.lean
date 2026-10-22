-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.eventual_weighted_generation_implies_eventual_surjective_weighted_sections
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung
-- created : 2026-10-21T07:07:37.858566+00:00
-- url     : https://prove2.me/submissions/72260df0-962f-4805-8281-8daa8820a3c5

import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Tactic

open scoped BigOperators

theorem solution
    {d : Nat} (I : Ideal (MvPolynomial (Fin d) Complex))
    (w : Fin d → Rat) (rho : Rat) (eps : Real)
    (hgen : ∃ N : Nat, ∀ n : Nat, N ≤ n →
      Function.Surjective
        (fun q : {q : MvPolynomial (Fin d) Complex //
              ∀ a ∈ q.support,
                ∑ i, (w i : Real) * (a i : Real) ≤
                  (n : Real) * ((rho : Real) + eps)} =>
          Ideal.Quotient.mk (I ^ n) q.1)) :
    ∃ N : Nat, ∀ n : Nat, N ≤ n →
      ∀ p : MvPolynomial (Fin d) Complex,
        ∃ q : MvPolynomial (Fin d) Complex,
          p - q ∈ I ^ n ∧
          ∀ a ∈ q.support,
            ∑ i, (w i : Real) * (a i : Real) ≤
              (n : Real) * ((rho : Real) + eps) := by
  obtain ⟨N, hN⟩ := hgen
  refine ⟨N, fun n hn p => ?_⟩
  obtain ⟨q, hq⟩ := hN n hn (Ideal.Quotient.mk (I ^ n) p)
  refine ⟨q.1, ?_, q.2⟩
  exact (Ideal.Quotient.eq).mp hq.symm
