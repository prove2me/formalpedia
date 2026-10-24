-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.weighted_relation_gives_coordinate_power
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T09:51:20.555919+00:00
-- url     : https://prove2.me/submissions/e4bf59d4-826a-4182-abba-cc55a9f9d513

import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_relation_constant_coeff_zero
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_positive_coeff_implies_coordinate_power

open scoped BigOperators

theorem solution
    {d : Nat} (w : Fin d → ℚ) (hw : ∀ i, 0 < (w i : ℝ))
    (D : Nat) (hD : 0 < D)
    (m : Nat) (p : Fin m → MvPolynomial (Fin d) ℂ)
    (hp : ∀ j, MvPolynomial.IsWeightedHomogeneous w (p j) (D : ℚ))
    (i : Fin d) (q : Polynomial ℂ) (hq : q ≠ 0)
    (hqI : Polynomial.aeval (MvPolynomial.X i) q ∈ Ideal.span (Set.range p)) :
    ∃ n : Nat, 0 < n ∧
      (MvPolynomial.X i : MvPolynomial (Fin d) ℂ) ^ n ∈ Ideal.span (Set.range p) := by
  let n := q.natDegree
  have hn : q.coeff n ≠ 0 := by
    dsimp [n]
    exact Polynomial.leadingCoeff_ne_zero.mpr hq
  have hconst :
      q.coeff 0 = 0 :=
    OAI.PiExponent.FormalInterpolation.relation_constant_coeff_zero
      (w := w) (hw := hw) (D := D) (hD := hD) (m := m) (p := p) (hp := hp)
      (i := i) (q := q) hqI
  have hnpos : 0 < n := by
    by_contra h
    have hn0 : n = 0 := Nat.eq_zero_of_not_pos h
    apply hn
    rw [hn0]
    exact hconst
  exact ⟨n, hnpos,
    OAI.PiExponent.FormalInterpolation.positive_coeff_implies_coordinate_power
      (w := w) (hw := hw) (D := D) (hD := hD) (m := m) (p := p) (hp := hp)
      (i := i) (q := q) (n := n) hnpos hqI hn⟩