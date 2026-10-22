-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.bounded_representatives_to_monic_relations
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung
-- created : 2026-10-21T05:30:11.639406+00:00
-- url     : https://prove2.me/submissions/223ccaf2-e28e-4b55-b210-1dc502403c17

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Mathlib.Tactic

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

theorem solution
    {d : Nat} (I : Ideal (MvPolynomial (Fin d) Complex))
    (w : Fin d → Rat) (c : Rat) (k : Nat)
    (hrep : ∀ P : MvPolynomial (Fin d) Complex,
      ∃ R : MvPolynomial (Fin d) Complex,
        P - R ∈ I ^ k ∧
        ∀ v ∈ R.support,
          (∑ j, (w j : Real) * (v j : Real)) ≤ (k : Real) * (c : Real))
    (b : Fin d → Nat)
    (hlower : ∀ i, (k : Real) * (c : Real) < (w i : Real) * (b i : Real)) :
    ∃ F : Fin d → MvPolynomial (Fin d) Complex,
      (∀ i, F i ∈ I ^ k) ∧
      (∀ i, ∀ v ∈ (MvPolynomial.X i ^ b i - F i).support,
        (∑ j, (w j : Real) * (v j : Real)) < (w i : Real) * (b i : Real)) := by
  classical
  set F : Fin d → MvPolynomial (Fin d) Complex := fun i =>
    MvPolynomial.X i ^ b i - (hrep (MvPolynomial.X i ^ b i)).choose with hFdef
  have hFmem : ∀ i, F i ∈ I ^ k := by
    intro i
    have := (hrep (MvPolynomial.X i ^ b i)).choose_spec.1
    simpa only [hFdef] using this
  have hFsupp :
      ∀ i, ∀ v ∈ (MvPolynomial.X i ^ b i - F i).support,
        (∑ j, (w j : Real) * (v j : Real)) < (w i : Real) * (b i : Real) := by
    intro i v hv
    have hQ :
        MvPolynomial.X i ^ b i - F i =
          (hrep (MvPolynomial.X i ^ b i)).choose := by
      rw [hFdef]; ring
    rw [hQ] at hv
    have hle := (hrep (MvPolynomial.X i ^ b i)).choose_spec.2 v hv
    exact lt_of_le_of_lt hle (hlower i)
  exact ⟨F, hFmem, hFsupp⟩
