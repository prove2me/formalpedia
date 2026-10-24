-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.origin_support_powers_20261023_22
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T18:38:34.312889+00:00
-- url     : https://prove2.me/submissions/77cdd6a5-f428-4b4b-899e-6f940199a973

import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_vanishing_power_mem_span

open scoped BigOperators

 theorem solution
    {d m : Nat} (q : Fin m → MvPolynomial (Fin d) Complex)
    (hzero : ∀ x : Fin d → Complex,
      (∀ j : Fin m, MvPolynomial.eval x (q j) = 0) →
      ∀ i : Fin d, x i = 0) :
    ∀ i : Fin d, ∃ N : Nat,
      0 < N ∧ (MvPolynomial.X i) ^ N ∈ Ideal.span (Set.range q) := by
  intro i
  have hvanish : ∀ x : Fin d → Complex,
      (∀ j : Fin m, MvPolynomial.eval x (q j) = 0) →
      MvPolynomial.eval x (MvPolynomial.X i) = 0 := by
    intro x hx
    simpa using hzero x hx i
  exact OAI.PiExponent.FormalInterpolation.vanishing_power_mem_span q
    (MvPolynomial.X i) hvanish