-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.span_components_mem_20261024
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-24T15:26:29.420113+00:00
-- url     : https://prove2.me/submissions/451f16f7-b555-477f-a009-bd89cb7e2322

import Mathlib.Data.Complex.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

theorem solution
    {d : Nat} (w : Fin d → Rat) (q : Rat)
    (S : Set (MvPolynomial (Fin d) Complex))
    (hhom : ∀ p ∈ S, ∃ g,
      p = MvPolynomial.weightedHomogeneousComponent
        (fun j => (w j : Rat)) q g) :
    ∀ p ∈ Ideal.span S, ∀ r : Rat,
      MvPolynomial.weightedHomogeneousComponent
        (fun j => (w j : Rat)) r p ∈ Ideal.span S := by
  classical
  let wt : Fin d → Rat := fun j => (w j : Rat)
  letI : DecidableEq Rat := Classical.decEq Rat
  letI := MvPolynomial.weightedGradedAlgebra Complex wt
  have hgens : ∀ x ∈ S,
      SetLike.IsHomogeneousElem
        (MvPolynomial.weightedHomogeneousSubmodule Complex wt) x := by
    intro x hx
    obtain ⟨g, hg⟩ := hhom x hx
    refine ⟨q, ?_⟩
    rw [hg]
    exact MvPolynomial.weightedHomogeneousComponent_mem wt g q
  have hspan : (Ideal.span S).IsHomogeneous
      (MvPolynomial.weightedHomogeneousSubmodule Complex wt) :=
    Ideal.homogeneous_span _ S hgens
  intro p hp r
  exact MvPolynomial.weightedHomogeneousComponent_mem_of_mem
    Complex wt hspan hp r