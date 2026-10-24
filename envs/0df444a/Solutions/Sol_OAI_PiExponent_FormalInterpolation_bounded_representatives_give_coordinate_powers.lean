-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.bounded_representatives_give_coordinate_powers
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T13:53:13.815818+00:00
-- url     : https://prove2.me/submissions/b2a63de0-6fe2-44b5-9191-bada4fb010a0

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

open scoped BigOperators

theorem solution
    {d : Nat} (I : Ideal (MvPolynomial (Fin d) Complex))
    (w : Fin d → Rat) (s : Nat) (D : Real)
    (rho : Rat) (eps C : Real)
    (hDcut : (s : Real) * ((rho : Real) + eps) + C < D)
    (hrepr : ∀ q : MvPolynomial (Fin d) Complex, ∃ p : MvPolynomial (Fin d) Complex,
      q - p ∈ I ^ s ∧
      ∀ a ∈ p.support,
        ∑ k, (w k : Real) * (a k : Real) ≤
          (s : Real) * ((rho : Real) + eps) + C)
    (hweights : ∀ i : Fin d, ∃ e : Nat, 0 < e ∧ (w i : Real) * (e : Real) = D) :
    ∀ i : Fin d, ∃ e : Nat, 0 < e ∧
      MvPolynomial.X i ^ e ∈
        Ideal.span (Set.range (fun f :
          {p : MvPolynomial (Fin d) Complex //
            p ∈ I ^ s ∧
            ∀ a ∈ p.support,
              ∑ k, (w k : Real) * (a k : Real) ≤ D} =>
          MvPolynomial.weightedHomogeneousComponent
            (fun k => (w k : Real)) D f.1)) := by
  classical
  intro i
  obtain ⟨e, hepos, hweight⟩ := hweights i
  refine ⟨e, hepos, ?_⟩
  let q : MvPolynomial (Fin d) Complex := MvPolynomial.X i ^ e
  obtain ⟨p, hpI, hpbound⟩ := hrepr q
  let wt : Fin d → Real := fun k => (w k : Real)
  have hqhom : q.IsWeightedHomogeneous wt D := by
    have hh : q.IsWeightedHomogeneous wt (e • wt i) := by
      dsimp [q]
      exact (MvPolynomial.isWeightedHomogeneous_X (R := Complex) (M := Real)
        (w := wt) (i := i)).pow e
    have hdegree : e • wt i = D := by
      simpa [wt, mul_comm] using hweight
    simpa [hdegree] using hh
  have hqcomp :
      MvPolynomial.weightedHomogeneousComponent wt D q = q :=
    MvPolynomial.weightedHomogeneousComponent_eq_self hqhom
  have hpcmp :
      MvPolynomial.weightedHomogeneousComponent wt D p = 0 := by
    apply MvPolynomial.weightedHomogeneousComponent_eq_zero'
    intro a ha
    have hpbound' : Finsupp.weight wt a ≤
        (s : Real) * ((rho : Real) + eps) + C := by
      simpa [Finsupp.weight_apply, Finsupp.sum_fintype, wt, mul_comm] using
        hpbound a ha
    exact ne_of_lt (lt_of_le_of_lt hpbound' hDcut)
  let f : {r : MvPolynomial (Fin d) Complex //
      r ∈ I ^ s ∧
      ∀ a ∈ r.support, ∑ k, (w k : Real) * (a k : Real) ≤ D} :=
    ⟨q - p, hpI, by
      intro a ha
      have hcoeff : MvPolynomial.coeff a (q - p) ≠ 0 :=
        MvPolynomial.mem_support_iff.mp ha
      have hcases : MvPolynomial.coeff a q ≠ 0 ∨ MvPolynomial.coeff a p ≠ 0 := by
        by_contra h
        push_neg at h
        apply hcoeff
        simp [h.1, h.2]
      rcases hcases with hq | hp
      · have hqa : a ∈ q.support := MvPolynomial.mem_support_iff.mpr hq
        have hqweight : Finsupp.weight wt a = D :=
          hqhom hq
        simpa [Finsupp.weight_apply, Finsupp.sum_fintype, wt, mul_comm] using
          (le_of_eq hqweight)
      · have hpa : a ∈ p.support := MvPolynomial.mem_support_iff.mpr hp


        exact le_trans (hpbound a hpa) (le_of_lt hDcut)⟩
  have hcomponent :
      MvPolynomial.weightedHomogeneousComponent wt D f.1 = q := by
    change MvPolynomial.weightedHomogeneousComponent wt D (q - p) = q
    rw [map_sub, hqcomp, hpcmp, sub_zero]
  apply Ideal.subset_span
  apply Set.mem_range.mpr
  exact ⟨f, hcomponent⟩