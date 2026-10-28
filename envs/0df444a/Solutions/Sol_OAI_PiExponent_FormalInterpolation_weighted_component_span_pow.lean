-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.weighted_component_span_pow
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-24T04:37:28.331091+00:00
-- url     : https://prove2.me/submissions/32b96fc5-cace-42d8-b241-ca1597a56ad7

import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_weighted_component_span_pow_span_power
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_weighted_component_span_pow_product

open scoped BigOperators

theorem solution
    {d : Nat} (I : Ideal (MvPolynomial (Fin d) Complex))
    (w : Fin d → Rat) (s m n : Nat) (q D : Rat)
    (hs : 0 < s) (hm : 0 < m) (hD : q * (m : Rat) = D)
    (f : MvPolynomial (Fin d) Complex)
    (hrel : f ^ n ∈ Ideal.span (Set.range (fun (p :
      {g : MvPolynomial (Fin d) Complex //
        g ∈ I ^ s ∧
        ∀ a ∈ g.support,
          ∑ j, (w j : Real) * (a j : Real) ≤ (q : Real)}) =>
      MvPolynomial.weightedHomogeneousComponent
        (fun j => (w j : ℚ)) q p.1))) :
    f ^ (n * m) ∈ Ideal.span {h : MvPolynomial (Fin d) Complex |
      ∃ g : MvPolynomial (Fin d) Complex,
        g ∈ I ^ (s * m) ∧
        (∀ a ∈ g.support,
          ∑ k, (w k : Real) * (a k : Real) ≤ (D : Real)) ∧
        h = MvPolynomial.weightedHomogeneousComponent
          (fun k => (w k : ℚ)) D g} := by
  have hprod : ∀ u : Fin m → {g : MvPolynomial (Fin d) Complex //
      g ∈ I ^ s ∧ ∀ a ∈ g.support,
        ∑ j, (w j : Real) * (a j : Real) ≤ (q : Real)},
      (∏ i, MvPolynomial.weightedHomogeneousComponent
        (fun j => (w j : ℚ)) q (u i).1) ∈
        Ideal.span {h : MvPolynomial (Fin d) Complex |
          ∃ g : MvPolynomial (Fin d) Complex,
            g ∈ I ^ (s * m) ∧
            (∀ a ∈ g.support,
              ∑ k, (w k : Real) * (a k : Real) ≤ (D : Real)) ∧
            h = MvPolynomial.weightedHomogeneousComponent
              (fun k => (w k : ℚ)) D g} := by
    intro u
    exact OAI.PiExponent.FormalInterpolation.weighted_component_span_pow_product
      I w s m q D hs hD u
  have hpow := OAI.PiExponent.FormalInterpolation.weighted_component_span_pow_span_power
    (g := fun (p : {g : MvPolynomial (Fin d) Complex //
      g ∈ I ^ s ∧ ∀ a ∈ g.support,
        ∑ j, (w j : Real) * (a j : Real) ≤ (q : Real)}) =>
      MvPolynomial.weightedHomogeneousComponent (fun j => (w j : ℚ)) q p.1)
    (m := m) (T := {h : MvPolynomial (Fin d) Complex |
      ∃ g : MvPolynomial (Fin d) Complex,
        g ∈ I ^ (s * m) ∧
        (∀ a ∈ g.support,
          ∑ k, (w k : Real) * (a k : Real) ≤ (D : Real)) ∧
        h = MvPolynomial.weightedHomogeneousComponent (fun k => (w k : ℚ)) D g})
    (x := f ^ n) hrel hprod
  simpa [pow_mul] using hpow