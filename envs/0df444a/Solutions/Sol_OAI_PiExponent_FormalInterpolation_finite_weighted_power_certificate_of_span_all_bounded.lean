-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.finite_weighted_power_certificate_of_span_all_bounded
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T08:34:51.049739+00:00
-- url     : https://prove2.me/submissions/e878fb66-26f5-47d8-8958-0f622d6633be

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_finite_subfamily_span

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

noncomputable section

theorem solution
    {d : Nat} (I : Ideal (MvPolynomial (Fin d) Complex))
    (w : Fin d → Rat) (s : Nat) (D : Real)
    (hspan : ∀ i : Fin d, ∃ e : Nat, 0 < e ∧
      MvPolynomial.X i ^ e ∈
        Ideal.span (Set.range (fun f :
          {p : MvPolynomial (Fin d) Complex //
            p ∈ I ^ s ∧
            ∀ a ∈ p.support,
              ∑ k, (w k : Real) * (a k : Real) ≤ D} =>
          MvPolynomial.weightedHomogeneousComponent
            (fun k => (w k : Real)) D f.1))) :
    ∃ n : Nat, ∃ f : Fin n → MvPolynomial (Fin d) Complex,
      (∀ j, f j ∈ I ^ s) ∧
      (∀ j, ∀ a ∈ (f j).support,
        ∑ k, (w k : Real) * (a k : Real) ≤ D) ∧
      ∀ i : Fin d, ∃ e : Nat, 0 < e ∧
        MvPolynomial.X i ^ e ∈
          Ideal.span (Set.range (fun j =>
            MvPolynomial.weightedHomogeneousComponent
              (fun k => (w k : Real)) D (f j))) := by
  classical
  let P := {p : MvPolynomial (Fin d) Complex //
    p ∈ I ^ s ∧ ∀ a ∈ p.support,
      ∑ k, (w k : Real) * (a k : Real) ≤ D}
  let g : P → MvPolynomial (Fin d) Complex := fun p =>
    MvPolynomial.weightedHomogeneousComponent (fun k => (w k : Real)) D p.1
  let x : Fin d → MvPolynomial (Fin d) Complex := fun i =>
    MvPolynomial.X i ^ Classical.choose (hspan i)
  have hx : ∀ i, x i ∈ Ideal.span (Set.range g) := by
    intro i
    exact (Classical.choose_spec (hspan i)).2
  obtain ⟨n, q, hq⟩ :=
    OAI.PiExponent.FormalInterpolation.finite_subfamily_span
      (R := MvPolynomial (Fin d) Complex) (α := Fin d) (ι := P)
      x g hx
  refine ⟨n, fun j => (q j).1, ?_, ?_, ?_⟩
  · intro j
    exact (q j).property.1
  · intro j a ha
    exact (q j).property.2 a ha
  · intro i
    refine ⟨Classical.choose (hspan i), (Classical.choose_spec (hspan i)).1, ?_⟩
    have hi := hq i
    simpa [x, g] using hi

