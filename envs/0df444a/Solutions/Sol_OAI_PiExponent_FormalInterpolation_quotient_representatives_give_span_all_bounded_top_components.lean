-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.quotient_representatives_give_span_all_bounded_top_components
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T08:50:37.324128+00:00
-- url     : https://prove2.me/submissions/469d8659-a132-4cde-998b-723b041798b6

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_exists_common_weight_degree
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_bounded_representatives_give_coordinate_powers

open scoped BigOperators

theorem solution
    {d : Nat} (I : Ideal (MvPolynomial (Fin d) Complex))
    (w : Fin d → Rat) (hw : ∀ i, 0 < (w i : Real))
    (rho : Rat) (hrho : 0 ≤ rho)
    (R : Real) (hR : (rho : Real) < R)
    (eps : Real) (heps : 0 < eps)
    (C : Real) (hC : 0 ≤ C) (N : Nat)
    (hrate : (rho : Real) + eps < R)
    (hrepr : ∀ n : Nat, N ≤ n →
      ∀ q : MvPolynomial (Fin d) Complex, ∃ p : MvPolynomial (Fin d) Complex,
        q - p ∈ I ^ n ∧
        ∀ a ∈ p.support,
          ∑ k, (w k : Real) * (a k : Real) ≤
            (n : Real) * ((rho : Real) + eps) + C) :
    ∃ s : Nat, 0 < s ∧
      ∃ D : Real, 0 < D ∧ D < (s : Real) * R ∧
        ∀ i : Fin d, ∃ e : Nat, 0 < e ∧
          MvPolynomial.X i ^ e ∈
            Ideal.span (Set.range (fun f :
              {p : MvPolynomial (Fin d) Complex //
                p ∈ I ^ s ∧
                ∀ a ∈ p.support,
                  ∑ k, (w k : Real) * (a k : Real) ≤ D} =>
              MvPolynomial.weightedHomogeneousComponent
                (fun k => (w k : Real)) D f.1)) := by
  obtain ⟨s, hs, hsN, D, hD, hDcut, hDR, hweights⟩ :=
    OAI.PiExponent.FormalInterpolation.exists_common_weight_degree
      (w := w) hw rho hrho R hR eps heps C hC N hrate
  have hrepr_s : ∀ q : MvPolynomial (Fin d) Complex, ∃ p : MvPolynomial (Fin d) Complex,
      q - p ∈ I ^ s ∧
      ∀ a ∈ p.support,
        ∑ k, (w k : Real) * (a k : Real) ≤
          (s : Real) * ((rho : Real) + eps) + C := by
    intro q
    exact hrepr s hsN q
  refine ⟨s, hs, D, hD, hDR, ?_⟩
  exact OAI.PiExponent.FormalInterpolation.bounded_representatives_give_coordinate_powers
    (I := I) (w := w) (s := s) (D := D)
    (rho := rho) (eps := eps) (C := C)
    (hDcut := hDcut) (hrepr := hrepr_s) hweights