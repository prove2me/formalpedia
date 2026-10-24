-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.monomial_mem_bounded_span_of_lower_weight_step
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T13:27:56.26582+00:00
-- url     : https://prove2.me/submissions/0953421f-1a6f-4019-a15e-f54b8679b3b1

import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_monomial_mem_lower_weight_span_of_lower_weight_step

open scoped BigOperators

theorem solution {d : Nat} (A : Subalgebra ℂ (MvPolynomial (Fin d) ℂ))
    (W : Fin d → Nat) (n : Fin d → Nat)
    (hred : ∀ i : Fin d,
      (MvPolynomial.X i : MvPolynomial (Fin d) ℂ) ^ n i ∈
        Submodule.span A {f : MvPolynomial (Fin d) ℂ |
          ∃ a : Fin d →₀ Nat,
            (∑ k : Fin d, a k * W k) < n i * W i ∧
              f = MvPolynomial.monomial a (1 : ℂ)})
    (e : Fin d →₀ Nat) (hover : ∃ i : Fin d, n i ≤ e i) :
    MvPolynomial.monomial e (1 : ℂ) ∈
      Submodule.span A
        ({f : MvPolynomial (Fin d) ℂ |
            ∃ a : Fin d →₀ Nat,
              (∀ i, a i < n i) ∧ f = MvPolynomial.monomial a (1 : ℂ)} ∪
          {f : MvPolynomial (Fin d) ℂ |
            ∃ b : Fin d →₀ Nat,
              (∑ k : Fin d, b k * W k) < (∑ k : Fin d, e k * W k) ∧
                f = MvPolynomial.monomial b (1 : ℂ)}) := by
  have hlower :=
    OAI.PiExponent.FormalInterpolation.monomial_mem_lower_weight_span_of_lower_weight_step
      (A := A) (W := W) (n := n) hred e hover
  exact Submodule.span_mono (R := A)
    (fun f hf => Set.mem_union_right _ hf) hlower