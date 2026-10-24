-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.rational_degree_initial_components_to_integer_degree
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-24T04:12:12.708989+00:00
-- url     : https://prove2.me/submissions/0b8b31e2-85b6-4d9e-95e0-f3cb211fc378
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_rational_degree_integer_multiple
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_weighted_component_span_pow

open scoped BigOperators

theorem solution
    {d : Nat} (I : Ideal (MvPolynomial (Fin d) Complex))
    (w : Fin d → Rat) (R : Real) (s B : Nat) (q : Rat)
    (hs : 0 < s) (hB : (B : Real) < (s : Real) * R)
    (hq : 0 < q) (hqB : (q : Real) ≤ (B : Real))
    (hcoords : ∀ i : Fin d, ∃ n : Nat, 0 < n ∧
      MvPolynomial.X i ^ n ∈ Ideal.span (Set.range (fun (p :
        {g : MvPolynomial (Fin d) Complex //
          g ∈ I ^ s ∧
          ∀ a ∈ g.support,
            ∑ j, (w j : Real) * (a j : Real) ≤ (q : Real)}) =>
        MvPolynomial.weightedHomogeneousComponent
          (fun j => (w j : ℚ)) q p.1))) :
    ∃ s' : Nat, 0 < s' ∧ ∃ D : Nat,
      (D : Real) < (s' : Real) * R ∧ 0 < D ∧
      ∀ i : Fin d, ∃ n : Nat, 0 < n ∧
        MvPolynomial.X i ^ n ∈ Ideal.span {h : MvPolynomial (Fin d) Complex |
          ∃ g : MvPolynomial (Fin d) Complex,
            g ∈ I ^ s' ∧
            (∀ a ∈ g.support,
              ∑ k, (w k : Real) * (a k : Real) ≤ (D : Real)) ∧
            h = MvPolynomial.weightedHomogeneousComponent
              (fun k => (w k : ℚ)) (D : ℚ) g} := by
  obtain ⟨m, D, hm, hDpos, hD, hDslope⟩ :=
    OAI.PiExponent.FormalInterpolation.rational_degree_integer_multiple
      s q R B hs hB hq hqB
  refine ⟨s * m, Nat.mul_pos hs hm, D, hDslope, hDpos, ?_⟩
  intro i
  obtain ⟨n, hn, hrel⟩ := hcoords i
  refine ⟨n * m, Nat.mul_pos hn hm, ?_⟩
  exact OAI.PiExponent.FormalInterpolation.weighted_component_span_pow
    I w s m n q D hs hm hD (MvPolynomial.X i) hrel
