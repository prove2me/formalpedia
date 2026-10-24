-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.bounded_sections_finite_witness_20261023_22
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T18:38:20.279563+00:00
-- url     : https://prove2.me/submissions/90b8e3e5-e005-4794-a9d1-1f1d455e434b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_finite_subfamily_of_polynomial_witnesses_20261023_22

open scoped BigOperators

theorem solution
    {d : Nat} (I : Ideal (MvPolynomial (Fin d) Complex))
    (w : Fin d → Rat) (s D : Nat)
    (hpoint : ∀ x : Fin d → Complex,
      (∃ i : Fin d, x i ≠ 0) →
      ∃ g : MvPolynomial (Fin d) Complex,
        g ∈ I ^ s ∧
        (∀ a ∈ g.support,
          ∑ k, (w k : Real) * (a k : Real) ≤ (D : Real)) ∧
        MvPolynomial.eval x
          (MvPolynomial.weightedHomogeneousComponent
            (fun k => (w k : ℚ)) (D : ℚ) g) ≠ 0) :
    ∃ m : Nat, ∃ g : Fin m → MvPolynomial (Fin d) Complex,
      (∀ j, g j ∈ I ^ s) ∧
      (∀ j, ∀ a ∈ (g j).support,
        ∑ k, (w k : Real) * (a k : Real) ≤ (D : Real)) ∧
      ∀ x : Fin d → Complex,
        (∀ j : Fin m,
          MvPolynomial.eval x
            (MvPolynomial.weightedHomogeneousComponent
              (fun k => (w k : ℚ)) (D : ℚ) (g j)) = 0) →
        ∀ i : Fin d, x i = 0 := by
  classical
  let P : Type :=
    {g : MvPolynomial (Fin d) Complex //
      g ∈ I ^ s ∧
        ∀ a ∈ g.support,
          ∑ k, (w k : Real) * (a k : Real) ≤ (D : Real)}
  let F : P → MvPolynomial (Fin d) Complex := fun p =>
    MvPolynomial.weightedHomogeneousComponent
      (fun k => (w k : ℚ)) (D : ℚ) p.1
  have hF : ∀ x : Fin d → Complex,
      (∀ p : P, MvPolynomial.eval x (F p) = 0) →
        ∀ i : Fin d, x i = 0 := by
    intro x hz
    by_contra hzero
    have hx : ∃ i : Fin d, x i ≠ 0 := by
      by_contra h
      push_neg at h
      exact hzero h
    obtain ⟨g, hgI, hgbound, hgeval⟩ := hpoint x hx
    exact hgeval (hz ⟨g, hgI, hgbound⟩)
  obtain ⟨m, idx, hfinite⟩ :=
    OAI.PiExponent.FormalInterpolation.finite_subfamily_of_polynomial_witnesses_20261023_22
      F hF
  refine ⟨m, fun j => (idx j).1, ?_, ?_, ?_⟩
  · intro j
    exact (idx j).2.1
  · intro j a ha
    exact (idx j).2.2 a ha
  · intro x hz
    apply hfinite x
    intro j
    exact hz j