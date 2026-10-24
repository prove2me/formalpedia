-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.bounded_sections_span_transfer
-- status  : ACCEPTED   (disprove)
-- author  : @Eyal1990
-- created : 2026-10-23T19:44:37.937619+00:00
-- url     : https://prove2.me/submissions/23948381-2cb2-4de8-9d97-ff77a22a2cd3

import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

open scoped BigOperators

theorem solution : ¬ (∀ {d : Nat} (I : Ideal (MvPolynomial (Fin d) Complex))
    (s : Nat) (S : Finset (MvPolynomial (Fin d) Complex))
    (hS : ∀ f ∈ S, f ∈ I ^ s)
    (w : Fin d → Rat) (rho : Rat) (eps : Real)
    (hcoordinates : ∀ i : Fin d, ∃ n : Nat, 0 < n ∧
      MvPolynomial.X i ^ n ∈ Ideal.span (S : Set (MvPolynomial (Fin d) Complex)) ∧
      (n : Real) * (w i : Real) < (s : Real) * ((rho : Real) + eps)),
    ∀ i : Fin d, ∃ s' n : Nat, 0 < s' ∧ 0 < n ∧
      MvPolynomial.X i ^ n ∈ I ^ s' ∧
      (n : Real) * (w i : Real) < (s' : Real) * ((rho : Real) + eps)) := by
  intro h
  let R := MvPolynomial (Fin 1) Complex
  let I : Ideal R := ⊥
  let S : Finset R := {MvPolynomial.X 0}
  let w : Fin 1 → Rat := fun _ => -1
  let rho : Rat := 0
  let eps : Real := 0
  have hS : ∀ f ∈ S, f ∈ I ^ 0 := by
    intro f hf
    simp [I]
  have hcoordinates : ∀ i : Fin 1, ∃ n : Nat, 0 < n ∧
      MvPolynomial.X i ^ n ∈ Ideal.span (S : Set R) ∧
      (n : Real) * (w i : Real) < ((0 : Nat) : Real) * ((rho : Real) + eps) := by
    intro i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    refine ⟨1, by norm_num, ?_, by norm_num [w, rho, eps]⟩
    apply Ideal.subset_span
    simp [S]
  have hout := h (d := 1) I 0 S hS w rho eps hcoordinates
  obtain ⟨s', n, hs', hn, hmem, hbound⟩ := hout 0
  have hxzero : (MvPolynomial.X (0 : Fin 1) : R) ^ n = 0 := by
    simpa [I, Nat.ne_of_gt hs'] using hmem
  have hxne : (MvPolynomial.X (0 : Fin 1) : R) ^ n ≠ 0 := by
    exact pow_ne_zero n (MvPolynomial.X_ne_zero (0 : Fin 1))
  exact hxne hxzero