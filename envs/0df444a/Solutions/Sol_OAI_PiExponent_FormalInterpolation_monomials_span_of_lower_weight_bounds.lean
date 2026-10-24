-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.monomials_span_of_lower_weight_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T13:02:54.879759+00:00
-- url     : https://prove2.me/submissions/a05e1b3b-66ec-4d5c-96cb-b02f3eaf5abf

import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_monomial_mem_bounded_span_of_lower_weight

open scoped BigOperators

theorem solution {d : Nat} (A : Subalgebra ℂ (MvPolynomial (Fin d) ℂ)) (W : Fin d → Nat) (hW : ∀ i, 0 < W i) (n : Fin d → Nat) (hn : ∀ i, 0 < n i) (hred : ∀ i : Fin d, (MvPolynomial.X i : MvPolynomial (Fin d) ℂ) ^ n i ∈ Submodule.span A {f : MvPolynomial (Fin d) ℂ | ∃ a : Fin d →₀ Nat, (∑ k : Fin d, a k * W k) < n i * W i ∧ f = MvPolynomial.monomial a (1 : ℂ)}) : ∀ e : Fin d →₀ Nat, MvPolynomial.monomial e (1 : ℂ) ∈ Submodule.span A {f : MvPolynomial (Fin d) ℂ | ∃ a : Fin d →₀ Nat, (∀ i, a i < n i) ∧ f = MvPolynomial.monomial a (1 : ℂ)} := by
  classical
  intro e
  let wt : (Fin d →₀ Nat) → Nat := fun b => ∑ k : Fin d, b k * W k
  have hmain : ∀ m : Nat, ∀ b : Fin d →₀ Nat, wt b = m → MvPolynomial.monomial b (1 : ℂ) ∈ Submodule.span A {f : MvPolynomial (Fin d) ℂ | ∃ a : Fin d →₀ Nat, (∀ i, a i < n i) ∧ f = MvPolynomial.monomial a (1 : ℂ)} := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
        intro b hb
        exact OAI.PiExponent.FormalInterpolation.monomial_mem_bounded_span_of_lower_weight A W hW n hn hred b (fun c hc => by
          have hc' : wt c < wt b := by simpa [wt] using hc
          exact ih (wt c) (by simpa [hb] using hc') c rfl)
  exact hmain (wt e) e rfl