-- Prove2me | solution 1 for MasulloRH.signed_displacement_moments_determine_origin_atom
-- status  : ACCEPTED   (prove)
-- author  : @Yi
-- created : 2026-11-21T14:23:15.162835+00:00
-- url     : https://prove2.me/submissions/d91a09ce-f4f3-43d2-b1a6-a887ef29fb73

import Mathlib
open Polynomial
theorem solution (s : Set ℝ) [CompactSpace s] (a : s) (ha : (a : ℝ) = 1)
    (w : C(s, ℝ)ˣ) (L : C(s, ℝ) →L[ℝ] ℝ)
    (mom : ∀ n : ℕ, L ((1 - toContinuousMapOnAlgHom s X) * (w : C(s, ℝ)) *
      (toContinuousMapOnAlgHom s X)^n) = 0) :
    ∀ f : C(s, ℝ), L f = L 1 * f a := by
  let y := toContinuousMapOnAlgHom s X
  let D : C(s, ℝ) →L[ℝ] ℝ := L - L 1 • ContinuousMap.evalCLM ℝ a
  have Dval (f : C(s, ℝ)) : D f = L f - L 1 * f a := rfl
  have ya : y a = 1 := by simpa [y] using ha
  have extend (b : C(s, ℝ)) (hb : ∀ n : ℕ, D (b * y^n) = 0)
      (f : C(s, ℝ)) : D (b * f) = 0 := by
    have hc : IsClosed {u : C(s, ℝ) | D (b * u) = 0} :=
      isClosed_eq (D.continuous.comp (continuous_const.mul continuous_id)) continuous_const
    have hs : (polynomialFunctions s : Set C(s, ℝ)) ⊆ {u | D (b * u) = 0} := by
      rw [polynomialFunctions_coe]
      rintro _ ⟨p, rfl⟩
      change D (b * toContinuousMapOnAlgHom s p) = 0
      induction p using Polynomial.induction_on' with
      | add p q hp hq => simp only [map_add, mul_add, hp, hq, add_zero]
      | monomial n c =>
        have e : toContinuousMapOnAlgHom s (monomial n c) = c • y^n := by
          ext x
          simp [y, mul_comm]
        rw [e, mul_smul_comm, map_smul, hb, smul_zero]
    have hf : f ∈ (polynomialFunctions s).topologicalClosure := by
      rw [polynomialFunctions.topologicalClosure]; trivial
    exact (closure_minimal hs hc) hf
  have weighted (f : C(s, ℝ)) : D (((1-y) * (w : C(s, ℝ))) * f) = 0 := by
    apply extend
    intro n
    rw [Dval, mom]
    simp [ya]
  have step (f : C(s, ℝ)) : D ((1-y)*f) = 0 := by
    simpa [mul_assoc] using weighted ((↑(w⁻¹) : C(s, ℝ))*f)
  have powers (n : ℕ) : D (y^n) = 0 := by
    induction n with
    | zero => simp [Dval]
    | succ n ih =>
      have e := step (y^n)
      rw [sub_mul, one_mul, ← pow_succ', map_sub, ih] at e
      simpa using e
  intro f
  have e : D ((1 : C(s, ℝ))*f) = 0 := extend 1 (by simpa using powers) f
  simpa [Dval, sub_eq_zero] using e
