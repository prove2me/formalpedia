-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.weighted_relation_mem_lower_weight_span
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T13:05:57.139993+00:00
-- url     : https://prove2.me/submissions/b21a6fcc-e8c1-47b5-abc0-32e3b6a7fda8

import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_weighted_relation_coeff_mem_lower_weight_span
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_weighted_relation_sum_mem_lower_weight_span

open scoped BigOperators

theorem solution {d : Nat} (W : Fin d → Nat) (delta : Nat) (hdelta : 0 < delta)
    (n : Nat) (i : Fin d) (m : Nat) (p q : Fin m → MvPolynomial (Fin d) ℂ)
    (hq : ∀ j, ∀ a : Fin d →₀ Nat, a ∈ (q j).support →
      (∑ k : Fin d, (a k : ℤ) * (W k : ℤ)) =
        (n : ℤ) * (W i : ℤ) - (delta : ℤ)) :
    (∑ j, q j * p j) ∈ Submodule.span (Algebra.adjoin ℂ (Set.range p))
      {f : MvPolynomial (Fin d) ℂ |
        ∃ a : Fin d →₀ Nat, (∑ k : Fin d, a k * W k) < n * W i ∧
          f = MvPolynomial.monomial a (1 : ℂ)} := by
  apply OAI.PiExponent.FormalInterpolation.weighted_relation_sum_mem_lower_weight_span
    (W := W) (n := n) (i := i) (p := p) (q := q)
  intro j
  exact OAI.PiExponent.FormalInterpolation.weighted_relation_coeff_mem_lower_weight_span
    W delta hdelta n i (q j) (hq j)