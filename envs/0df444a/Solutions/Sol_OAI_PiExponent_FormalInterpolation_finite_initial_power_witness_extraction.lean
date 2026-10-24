-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.finite_initial_power_witness_extraction
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T17:13:17.557015+00:00
-- url     : https://prove2.me/submissions/8ed6f0d5-0412-44a5-b866-3385bce4f429

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_finite_power_witnesses_of_span_range

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

theorem solution
    {d : Nat} (I : Ideal (MvPolynomial (Fin d) Complex))
    (w : Fin d → Rat)
    (s : Nat) (hs : 0 < s)
    (D : Real) (hD : 0 < D)
    (hinitial : ∀ i : Fin d, ∃ e : Nat, 0 < e ∧
      MvPolynomial.X i ^ e ∈
        Ideal.span (Set.range (fun (p :
          {g : MvPolynomial (Fin d) Complex //
            g ∈ I ^ s ∧
            ∀ a ∈ g.support,
              ∑ j, (w j : Real) * (a j : Real) ≤ D}) =>
          MvPolynomial.weightedHomogeneousComponent
            (fun j => (w j : Real)) D p.1))) :
    ∃ k : Nat, ∃ f : Fin k → MvPolynomial (Fin d) Complex,
      (∀ j, f j ∈ I ^ s) ∧
      (∀ j, ∀ a ∈ (f j).support,
        ∑ i, (w i : Real) * (a i : Real) ≤ D) ∧
      (∀ i : Fin d, ∃ e : Nat, 0 < e ∧
        MvPolynomial.X i ^ e ∈
          Ideal.span (Set.range (fun j : Fin k =>
            MvPolynomial.weightedHomogeneousComponent
              (fun i => (w i : Real)) D (f j)))) := by
  let P : MvPolynomial (Fin d) Complex → Prop := fun p =>
    p ∈ I ^ s ∧ ∀ a ∈ p.support,
      ∑ j, (w j : Real) * (a j : Real) ≤ D
  let g : MvPolynomial (Fin d) Complex → MvPolynomial (Fin d) Complex :=
    fun p => MvPolynomial.weightedHomogeneousComponent
      (fun j => (w j : Real)) D p
  obtain ⟨k, f, hf⟩ :=
    OAI.PiExponent.FormalInterpolation.finite_power_witnesses_of_span_range
      (R := MvPolynomial (Fin d) Complex)
      (ι := Fin d)
      (α := MvPolynomial (Fin d) Complex)
      (fun i : Fin d => MvPolynomial.X i) P g hinitial
  refine ⟨k, fun j => (f j).1, ?_, ?_, ?_⟩
  · intro j
    exact (f j).2.1
  · intro j a ha
    exact (f j).2.2 a ha
  · intro i
    exact hf i