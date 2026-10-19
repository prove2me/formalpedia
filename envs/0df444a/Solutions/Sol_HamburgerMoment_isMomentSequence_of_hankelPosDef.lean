-- Prove2me | solution 1 for HamburgerMoment.isMomentSequence_of_hankelPosDef
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T22:14:11.335284+00:00
-- url     : https://prove2.me/submissions/0fcd7e85-2532-4ef5-8043-644a6fda10b2

import Theorems.Thm_Polynomial_haviland_real
import Definitions.Def_HamburgerMoment_Defs
import Theorems.Thm_Polynomial_isSumSq_of_eval_nonneg
import Mathlib.LinearAlgebra.Finsupp.LSum

open Polynomial MeasureTheory

set_option autoImplicit false

private noncomputable def momentL (m : ℕ → ℝ) : ℝ[X] →ₗ[ℝ] ℝ :=
  (Finsupp.lift ℝ ℝ ℕ m).comp
    ((AddMonoidAlgebra.coeffLinearEquiv ℝ).toLinearMap.comp
      (toFinsuppIsoLinear ℝ).toLinearMap)

private lemma momentL_monomial (m : ℕ → ℝ) (n : ℕ) (a : ℝ) :
    momentL m (monomial n a) = a * m n := by
  simp [momentL, Finsupp.lift_apply, Finsupp.sum_single_index]

private lemma momentL_mul (m : ℕ → ℝ) (p q : ℝ[X]) :
    momentL m (p*q) = ∑ i ∈ p.support, ∑ j ∈ q.support,
      p.coeff i * q.coeff j * m (i+j) := by
  have hp : p = ∑ i ∈ p.support, monomial i (p.coeff i) := p.sum_monomial_eq.symm
  have hq : q = ∑ j ∈ q.support, monomial j (q.coeff j) := q.sum_monomial_eq.symm
  calc
    _ = momentL m ((∑ i ∈ p.support, monomial i (p.coeff i)) *
        (∑ j ∈ q.support, monomial j (q.coeff j))) :=
      congrArg (momentL m) (congrArg₂ (·*·) hp hq)
    _ = _ := by
      simp only [Finset.sum_mul, Finset.mul_sum, map_sum, monomial_mul_monomial,
        momentL_monomial]
      exact Finset.sum_comm

open scoped ComplexOrder in
private lemma momentL_square_nonneg (m : ℕ → ℝ) (hm : HamburgerMoment.HankelPosDef m)
    (p : ℝ[X]) : 0 ≤ momentL m (p^2) := by
  classical
  let c : ℕ →₀ ℂ := (p.map (algebraMap ℝ ℂ)).toFinsupp.coeff
  have hs : c.support = p.support :=
    p.support_map_of_injective (f := algebraMap ℝ ℂ) Complex.ofReal_injective
  have he : HamburgerMoment.hankelForm m c = (momentL m (p^2) : ℂ) := by
    rw [pow_two, momentL_mul]
    simp only [HamburgerMoment.hankelForm, hs, Complex.ofReal_sum, Complex.ofReal_mul]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    have hc : ∀ i, c i = (p.coeff i : ℂ) := by intro i; exact coeff_map _ _
    rw [hc i, hc j]
    simp only [Complex.conj_ofReal]
    ring
  have h := hm c
  rw [he] at h
  exact_mod_cast h

private lemma momentL_nonneg (m : ℕ → ℝ) (hm : HamburgerMoment.HankelPosDef m)
    (p : ℝ[X]) (hp : ∀ x : ℝ, 0 ≤ p.eval x) : 0 ≤ momentL m p := by
  have hs := Polynomial.isSumSq_of_eval_nonneg p hp
  clear hp
  induction hs with
  | zero => simp only [map_zero, le_refl]
  | sq_add a hs ih =>
    rw [map_add]
    exact add_nonneg (by simpa only [pow_two] using momentL_square_nonneg m hm a) ih

private lemma momentL_X_pow (m : ℕ → ℝ) (n : ℕ) : momentL m (X^n) = m n := by
  rw [← monomial_one_right_eq_X_pow, momentL_monomial, one_mul]

theorem solution (m : ℕ → ℝ) (hm : HamburgerMoment.HankelPosDef m) :
    HamburgerMoment.IsMomentSequence m := by
  obtain ⟨μ, _, hμ⟩ := Polynomial.haviland_real Set.univ isClosed_univ (momentL m)
    (fun p hp => momentL_nonneg m hm p (fun x => hp x (Set.mem_univ x)))
  refine ⟨μ, fun n => ?_⟩
  simpa only [eval_pow, eval_X, momentL_X_pow] using hμ (X^n)
