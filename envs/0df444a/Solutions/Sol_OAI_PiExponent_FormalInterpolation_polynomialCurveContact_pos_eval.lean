-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.polynomialCurveContact_pos_eval
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T19:41:05.938071+00:00
-- url     : https://prove2.me/submissions/5e74f61e-3fcb-4b4d-a6f4-cef3632b59b4

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Mathlib
open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

theorem solution
    {d : Nat} {E : Type} [Field E] [Algebra Complex E]
    (nu : PolynomialCurvePlace E) (x : Fin d → E)
    (I : Ideal (MvPolynomial (Fin d) Complex))
    (hcontact : 0 < polynomialCurveIdealContact nu x I)
    (f : MvPolynomial (Fin d) Complex) (hf : f ∈ I) :
    (0 : WithTop Int) < nu.1 (MvPolynomial.aeval x f) := by
  classical
  have hchart : ∀ i, (0 : WithTop Int) ≤ nu.1 (x i) := by
    by_contra hcon
    unfold polynomialCurveIdealContact at hcontact
    rw [if_neg hcon] at hcontact; exact lt_irrefl _ hcontact
  have hpoly : ∀ P : MvPolynomial (Fin d) Complex, 0 ≤ nu.1 (MvPolynomial.aeval x P) := by
    intro P
    induction P using MvPolynomial.induction_on with
    | C b =>
      rw [MvPolynomial.aeval_C]
      by_cases hb : b = 0
      · subst hb; simp [AddValuation.map_zero]
      · rw [nu.2.1 b hb]
    | add p q hp hq => rw [map_add]; exact le_trans (le_min hp hq) (nu.1.map_add _ _)
    | mul_X p i hp =>
      rw [map_mul, nu.1.map_mul, MvPolynomial.aeval_X]; exact add_nonneg hp (hchart i)
  by_cases htop : nu.1 (MvPolynomial.aeval x f) = ⊤
  · rw [htop]; exact WithTop.coe_lt_top 0
  · obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.mp htop
    have hk0 : (0:ℤ) ≤ k := by have := hpoly f; rw [← hk] at this; exact_mod_cast this
    have hle : polynomialCurveIdealContact nu x I ≤ k.toNat := by
      unfold polynomialCurveIdealContact; rw [if_pos hchart]
      apply Nat.sInf_le
      exact ⟨f, hf, by rw [← hk]; congr 1; omega⟩
    have : (0:ℤ) < k := by omega
    rw [← hk]; exact_mod_cast this
