-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.monomials_span_of_degree_drop
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T12:47:23.904281+00:00
-- url     : https://prove2.me/submissions/4bd9653f-1b0d-440e-acd9-fd9a5d730379

import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_integer_weight_scale_for_family
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_integer_weighted_monomials_span

open scoped BigOperators

theorem solution {d : Nat} (w : Fin d → ℚ)
    (hw : ∀ i, 0 < (w i : ℝ)) (D : Nat) (hD : 0 < D) (m : Nat)
    (p : Fin m → MvPolynomial (Fin d) ℂ)
    (hrelations : ∀ i : Fin d, ∃ n : Nat, 0 < n ∧
      ∃ q : Fin m → MvPolynomial (Fin d) ℂ,
        (MvPolynomial.X i : MvPolynomial (Fin d) ℂ) ^ n = ∑ j, q j * p j ∧
        ∀ j, MvPolynomial.IsWeightedHomogeneous w (q j)
          ((n : ℚ) * w i - (D : ℚ))) :
    ∃ n : Fin d → Nat, (∀ i, 0 < n i) ∧
      ∀ e : Fin d →₀ Nat,
        MvPolynomial.monomial e (1 : ℂ) ∈
          Submodule.span (Algebra.adjoin ℂ (Set.range p))
            {f : MvPolynomial (Fin d) ℂ |
              ∃ a : Fin d →₀ Nat, (∀ i, a i < n i) ∧
                f = MvPolynomial.monomial a (1 : ℂ)} := by
  obtain ⟨S, hS, W, hW, hscale⟩ :=
    OAI.PiExponent.FormalInterpolation.integer_weight_scale_for_family w hw D m
  have hSD : 0 < S * D := Nat.mul_pos hS hD
  have hrelations' :
      ∀ i : Fin d, ∃ n : Nat, 0 < n ∧
        ∃ q : Fin m → MvPolynomial (Fin d) ℂ,
          (MvPolynomial.X i : MvPolynomial (Fin d) ℂ) ^ n = ∑ j, q j * p j ∧
          ∀ j, ∀ a : Fin d →₀ Nat, a ∈ (q j).support →
            (∑ k, (a k : ℤ) * (W k : ℤ)) =
              (n : ℤ) * (W i : ℤ) - ((S * D : Nat) : ℤ) := by
    intro i
    obtain ⟨n, hn, q, heq, hq⟩ := hrelations i
    refine ⟨n, hn, q, heq, ?_⟩
    intro j a ha
    exact hscale.2 i n q hq j a ha
  exact OAI.PiExponent.FormalInterpolation.integer_weighted_monomials_span
    W hW (S * D) hSD m p hrelations'