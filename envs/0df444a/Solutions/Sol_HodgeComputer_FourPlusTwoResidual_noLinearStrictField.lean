-- Prove2me | solution 1 for HodgeComputer.FourPlusTwoResidual.noLinearStrictField
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-11-15T06:57:32.580199+00:00
-- url     : https://prove2.me/submissions/69376220-759c-4776-ae46-7bf1b0cd1235

import Definitions.Def_HodgeComputerFourPlusTwoCore
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Data.Finsupp.BigOperators
import Mathlib.RingTheory.MvPolynomial.EulerIdentity

open MvPolynomial
open HodgeComputer.FourPlusTwoResidual

set_option autoImplicit false
noncomputable section

/-- The monomial `x₀³ x₂³`, i.e. the multi-index `(3,0,3,0)`. -/
private def m3030 : Fin 4 →₀ ℕ := Finsupp.single 0 3 + Finsupp.single 2 3

private def supp0 : Fin 4 →₀ ℕ := Finsupp.single 0 6
private def supp1 : Fin 4 →₀ ℕ := Finsupp.single 0 5 + Finsupp.single 1 1
private def supp2 : Fin 4 →₀ ℕ :=
  Finsupp.single 0 3 + Finsupp.single 1 1 + Finsupp.single 2 1 + Finsupp.single 3 1
private def supp3 : Fin 4 →₀ ℕ := Finsupp.single 0 1 + Finsupp.single 1 5
private def supp4 : Fin 4 →₀ ℕ :=
  Finsupp.single 0 1 + Finsupp.single 1 1 + Finsupp.single 2 3 + Finsupp.single 3 1
private def supp5 : Fin 4 →₀ ℕ := Finsupp.single 1 6
private def supp6 : Fin 4 →₀ ℕ := Finsupp.single 2 6
private def supp7 : Fin 4 →₀ ℕ := Finsupp.single 2 5 + Finsupp.single 3 1
private def supp8 : Fin 4 →₀ ℕ := Finsupp.single 2 1 + Finsupp.single 3 5
private def supp9 : Fin 4 →₀ ℕ := Finsupp.single 3 6

private lemma ne_by_coords {d e : Fin 4 →₀ ℕ}
    (h : d 0 ≠ e 0 ∨ d 1 ≠ e 1 ∨ d 2 ≠ e 2 ∨ d 3 ≠ e 3) : d ≠ e := by
  rintro rfl
  simp at h

private lemma term0_eq : (X 0 : MvPolynomial (Fin 4) ℂ) ^ 6 = monomial supp0 1 := by
  simp [supp0, X_pow_eq_monomial]

private lemma term1_eq :
    C (5 / 7 : ℂ) * X 0 ^ 5 * X 1 = monomial supp1 (5 / 7 : ℂ) := by
  unfold supp1
  rw [X_pow_eq_monomial, C_mul_monomial, mul_one, X, monomial_mul, mul_one]

private lemma term2_eq :
    C (5 / 7 : ℂ) * X 0 ^ 3 * X 1 * X 2 * X 3 = monomial supp2 (5 / 7 : ℂ) := by
  unfold supp2
  rw [X_pow_eq_monomial, C_mul_monomial, mul_one, X, monomial_mul, mul_one, X, monomial_mul,
    mul_one, X, monomial_mul, mul_one]

private lemma term3_eq :
    C (10 / 7 : ℂ) * X 0 * X 1 ^ 5 = monomial supp3 (10 / 7 : ℂ) := by
  unfold supp3
  rw [X, C_mul_monomial, mul_one, X_pow_eq_monomial, monomial_mul, mul_one]

private lemma term4_eq :
    C (10 / 7 : ℂ) * X 0 * X 1 * X 2 ^ 3 * X 3 = monomial supp4 (10 / 7 : ℂ) := by
  unfold supp4
  rw [X, C_mul_monomial, mul_one, X, monomial_mul, mul_one, X_pow_eq_monomial, monomial_mul,
    mul_one, X, monomial_mul, mul_one]

private lemma term5_eq : (X 1 : MvPolynomial (Fin 4) ℂ) ^ 6 = monomial supp5 1 := by
  simp [supp5, X_pow_eq_monomial]

private lemma term6_eq : (X 2 : MvPolynomial (Fin 4) ℂ) ^ 6 = monomial supp6 1 := by
  simp [supp6, X_pow_eq_monomial]

private lemma term7_eq :
    C (5 / 7 : ℂ) * X 2 ^ 5 * X 3 = monomial supp7 (5 / 7 : ℂ) := by
  unfold supp7
  rw [X_pow_eq_monomial, C_mul_monomial, mul_one, X, monomial_mul, mul_one]

private lemma term8_eq :
    C (15 / 7 : ℂ) * X 2 * X 3 ^ 5 = monomial supp8 (15 / 7 : ℂ) := by
  unfold supp8
  rw [X, C_mul_monomial, mul_one, X_pow_eq_monomial, monomial_mul, mul_one]

private lemma term9_eq : (X 3 : MvPolynomial (Fin 4) ℂ) ^ 6 = monomial supp9 1 := by
  simp [supp9, X_pow_eq_monomial]

private lemma coeff_core_of {d : Fin 4 →₀ ℕ}
    (h0 : d ≠ supp0) (h1 : d ≠ supp1) (h2 : d ≠ supp2) (h3 : d ≠ supp3) (h4 : d ≠ supp4)
    (h5 : d ≠ supp5) (h6 : d ≠ supp6) (h7 : d ≠ supp7) (h8 : d ≠ supp8) (h9 : d ≠ supp9) :
    coeff d core = 0 := by
  unfold core
  rw [coeff_add, coeff_add, coeff_add, coeff_add, coeff_add, coeff_add, coeff_add, coeff_add,
    coeff_add]
  rw [term0_eq, term1_eq, term2_eq, term3_eq, term4_eq, term5_eq, term6_eq, term7_eq, term8_eq,
    term9_eq]
  simp only [coeff_monomial, h0.symm, h1.symm, h2.symm, h3.symm, h4.symm, h5.symm, h6.symm,
    h7.symm, h8.symm, h9.symm]
  simp

private lemma coeff_m_coreSource : coeff m3030 coreSource = 1 := by
  unfold coreSource m3030
  have h : (X 0 : MvPolynomial (Fin 4) ℂ) ^ 3 * X 2 ^ 3 =
      monomial (Finsupp.single 0 3 + Finsupp.single 2 3) 1 := by
    rw [X_pow_eq_monomial, X_pow_eq_monomial, monomial_mul, mul_one]
  rw [h, coeff_monomial, if_pos rfl]

private lemma not_in_support (d : Fin 4 →₀ ℕ)
    (h0 : d 0 ≠ supp0 0 ∨ d 1 ≠ supp0 1 ∨ d 2 ≠ supp0 2 ∨ d 3 ≠ supp0 3)
    (h1 : d 0 ≠ supp1 0 ∨ d 1 ≠ supp1 1 ∨ d 2 ≠ supp1 2 ∨ d 3 ≠ supp1 3)
    (h2 : d 0 ≠ supp2 0 ∨ d 1 ≠ supp2 1 ∨ d 2 ≠ supp2 2 ∨ d 3 ≠ supp2 3)
    (h3 : d 0 ≠ supp3 0 ∨ d 1 ≠ supp3 1 ∨ d 2 ≠ supp3 2 ∨ d 3 ≠ supp3 3)
    (h4 : d 0 ≠ supp4 0 ∨ d 1 ≠ supp4 1 ∨ d 2 ≠ supp4 2 ∨ d 3 ≠ supp4 3)
    (h5 : d 0 ≠ supp5 0 ∨ d 1 ≠ supp5 1 ∨ d 2 ≠ supp5 2 ∨ d 3 ≠ supp5 3)
    (h6 : d 0 ≠ supp6 0 ∨ d 1 ≠ supp6 1 ∨ d 2 ≠ supp6 2 ∨ d 3 ≠ supp6 3)
    (h7 : d 0 ≠ supp7 0 ∨ d 1 ≠ supp7 1 ∨ d 2 ≠ supp7 2 ∨ d 3 ≠ supp7 3)
    (h8 : d 0 ≠ supp8 0 ∨ d 1 ≠ supp8 1 ∨ d 2 ≠ supp8 2 ∨ d 3 ≠ supp8 3)
    (h9 : d 0 ≠ supp9 0 ∨ d 1 ≠ supp9 1 ∨ d 2 ≠ supp9 2 ∨ d 3 ≠ supp9 3) :
    coeff d core = 0 := by
  apply coeff_core_of
  · exact ne_by_coords h0
  · exact ne_by_coords h1
  · exact ne_by_coords h2
  · exact ne_by_coords h3
  · exact ne_by_coords h4
  · exact ne_by_coords h5
  · exact ne_by_coords h6
  · exact ne_by_coords h7
  · exact ne_by_coords h8
  · exact ne_by_coords h9

private lemma eval_support_and_m :
    (m3030 0 = 3 ∧ m3030 1 = 0 ∧ m3030 2 = 3 ∧ m3030 3 = 0) ∧
    (supp0 0 = 6 ∧ supp0 1 = 0 ∧ supp0 2 = 0 ∧ supp0 3 = 0) ∧
    (supp1 0 = 5 ∧ supp1 1 = 1 ∧ supp1 2 = 0 ∧ supp1 3 = 0) ∧
    (supp2 0 = 3 ∧ supp2 1 = 1 ∧ supp2 2 = 1 ∧ supp2 3 = 1) ∧
    (supp3 0 = 1 ∧ supp3 1 = 5 ∧ supp3 2 = 0 ∧ supp3 3 = 0) ∧
    (supp4 0 = 1 ∧ supp4 1 = 1 ∧ supp4 2 = 3 ∧ supp4 3 = 1) ∧
    (supp5 0 = 0 ∧ supp5 1 = 6 ∧ supp5 2 = 0 ∧ supp5 3 = 0) ∧
    (supp6 0 = 0 ∧ supp6 1 = 0 ∧ supp6 2 = 6 ∧ supp6 3 = 0) ∧
    (supp7 0 = 0 ∧ supp7 1 = 0 ∧ supp7 2 = 5 ∧ supp7 3 = 1) ∧
    (supp8 0 = 0 ∧ supp8 1 = 0 ∧ supp8 2 = 1 ∧ supp8 3 = 5) ∧
    (supp9 0 = 0 ∧ supp9 1 = 0 ∧ supp9 2 = 0 ∧ supp9 3 = 6) := by
  unfold m3030 supp0 supp1 supp2 supp3 supp4 supp5 supp6 supp7 supp8 supp9
  simp [Finsupp.add_apply]

private lemma coeff_m_core : coeff m3030 core = 0 := by
  have ev := eval_support_and_m
  rcases ev with ⟨hm, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  apply not_in_support
  all_goals (simp [hm, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9]; try decide)

/-- A degree-1 homogeneous polynomial is a linear form. -/
private lemma eq_sum_linear {p : MvPolynomial (Fin 4) ℂ} (hp : p.IsHomogeneous 1) :
    p = ∑ j : Fin 4, C (coeff (Finsupp.single j 1) p) * (X (R := ℂ) j) := by
  ext d
  rw [coeff_sum]
  simp only [coeff_C_mul]
  by_cases hd : d.degree = 1
  · have hsum : d.sum (fun _ n => n) = 1 := by
      change (∑ i ∈ d.support, d i) = 1
      rwa [Finsupp.degree_apply] at hd
    obtain ⟨j, rfl⟩ := (Finsupp.sum_eq_one_iff d).mp hsum
    have hx : ∀ x : Fin 4,
        coeff (Finsupp.single j 1) (X (R := ℂ) x) = if x = j then (1 : ℂ) else 0 := by
      intro x
      rw [coeff_X]
      by_cases h : Finsupp.single x 1 = Finsupp.single j 1
      · have : x = j := (Finsupp.single_left_inj (by decide : (1 : ℕ) ≠ 0)).mp h
        simp [this]
      · have : x ≠ j := by
          intro hx
          exact h (hx ▸ rfl)
        simp [h, this]
    have hxsum :
        (∑ x : Fin 4, coeff (Finsupp.single x 1) p * coeff (Finsupp.single j 1) (X (R := ℂ) x)) =
          ∑ x : Fin 4, coeff (Finsupp.single x 1) p * (if x = j then (1 : ℂ) else 0) := by
      apply Finset.sum_congr rfl
      intro x _
      exact congrArg (fun t => coeff (Finsupp.single x 1) p * t) (hx x)
    rw [hxsum]
    simp [mul_ite, mul_one, mul_zero, Finset.mem_univ]
  · have hp0 : coeff d p = 0 := hp.coeff_eq_zero hd
    have hr : ∀ j : Fin 4, coeff d (X (R := ℂ) j) = 0 := by
      intro j
      rw [coeff_X]
      split_ifs with hj
      · subst hj
        exact (hd (by simp [Finsupp.degree_single])).elim
      · rfl
    rw [hp0]
    symm
    refine (Finset.sum_eq_zero (s := (Finset.univ : Finset (Fin 4))) ?_)
    intro x _
    exact mul_eq_zero.mpr (Or.inr (hr x))

private lemma eval_neighbor (i j k : Fin 4) :
    (m3030 - Finsupp.single j 1 + Finsupp.single i 1 : Fin 4 →₀ ℕ) k =
      m3030 k - (if j = k then 1 else 0) + (if i = k then 1 else 0) := by
  rw [Finsupp.add_apply, Finsupp.tsub_apply]
  simp [Finsupp.single_apply]

private lemma coeff_core_at_m_or_neighbor (i j : Fin 4) :
    coeff (m3030 - Finsupp.single j 1 + Finsupp.single i 1) core = 0 := by
  fin_cases i <;> fin_cases j
  all_goals
    · have ev := eval_support_and_m
      rcases ev with ⟨hm, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9⟩
      apply not_in_support
      all_goals
        · simp only [eval_neighbor, hm, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9]
          try decide

private lemma coeff_m_directional (L : Fin 4 → MvPolynomial (Fin 4) ℂ)
    (hL : ∀ i, (L i).IsHomogeneous 1) :
    coeff m3030 (∑ i : Fin 4, pderiv i core * L i) = 0 := by
  rw [coeff_sum]
  refine Finset.sum_eq_zero ?_
  intro i _
  have hLin : L i = ∑ j : Fin 4, C (coeff (Finsupp.single j 1) (L i)) * X (R := ℂ) j :=
    eq_sum_linear (hL i)
  rw [hLin, Finset.mul_sum, coeff_sum]
  refine Finset.sum_eq_zero ?_
  intro j _
  rw [mul_comm (pderiv i core), mul_assoc, coeff_C_mul]
  rw [coeff_X_mul']
  split_ifs with hj
  · have hcoeff :
        coeff (m3030 - Finsupp.single j 1 : Fin 4 →₀ ℕ) (pderiv i core) =
          coeff ((m3030 - Finsupp.single j 1 : Fin 4 →₀ ℕ) + Finsupp.single i 1) core *
            ((m3030 - Finsupp.single j 1 : Fin 4 →₀ ℕ) i + 1) :=
      coeff_pderiv _ _
    rw [hcoeff, coeff_core_at_m_or_neighbor, zero_mul, mul_zero]
  · rw [mul_zero]

private lemma coeff_m_div_term (L : Fin 4 → MvPolynomial (Fin 4) ℂ)
    (hL : ∀ i, (L i).IsHomogeneous 1) :
    coeff m3030 (core * ∑ i : Fin 4, pderiv i (L i)) = 0 := by
  have hdiv : (∑ i : Fin 4, pderiv i (L i)).IsHomogeneous 0 :=
    IsHomogeneous.sum _ _ 0 (fun k _ => IsHomogeneous.pderiv (i := k) (hL k))
  have hC : (∑ i : Fin 4, pderiv i (L i)) = C (coeff 0 (∑ i : Fin 4, pderiv i (L i))) := by
    rw [← totalDegree_eq_zero_iff_eq_C, totalDegree_zero_iff_isHomogeneous]
    exact hdiv
  rw [hC, mul_comm, coeff_C_mul, coeff_m_core, mul_zero]

private lemma coeff_two_mul (p : MvPolynomial (Fin 4) ℂ) (d : Fin 4 →₀ ℕ) :
    coeff d (2 * p) = 2 * coeff d p := by
  rw [two_mul, coeff_add]
  ring

private lemma coeff_three_mul (p : MvPolynomial (Fin 4) ℂ) (d : Fin 4 →₀ ℕ) :
    coeff d (3 * p) = 3 * coeff d p := by
  have h : (3 : MvPolynomial (Fin 4) ℂ) = 1 + 1 + 1 := by norm_num
  rw [h, add_mul, add_mul, one_mul, coeff_add, coeff_add]
  ring

theorem solution :
    ¬ ∃ L : Fin 4 → MvPolynomial (Fin 4) ℂ,
      (∀ i, (L i).IsHomogeneous 1) ∧
      2 * coreSource - 2 * (∑ i, pderiv i core * L i)
        + 3 * core * (∑ i, pderiv i (L i)) = 0 := by
  rintro ⟨L, hL, hid⟩
  have hcoeff :
      coeff m3030
          (2 * coreSource - 2 * (∑ i, pderiv i core * L i)
            + 3 * core * (∑ i, pderiv i (L i))) = 0 := by
    rw [hid, coeff_zero]
  have hval :
      coeff m3030
          (2 * coreSource - 2 * (∑ i, pderiv i core * L i)
            + 3 * core * (∑ i, pderiv i (L i))) = 2 := by
    rw [coeff_add, coeff_sub]
    -- `2 * p` and `3 * core * div` use the polynomial coercion of a natural number.
    have h2p : coeff m3030 (2 * coreSource) = 2 := by
      rw [coeff_two_mul, coeff_m_coreSource, mul_one]
    have h2d : coeff m3030 (2 * ∑ i, pderiv i core * L i) = 0 := by
      rw [coeff_two_mul, coeff_m_directional L hL, mul_zero]
    have h3 : coeff m3030 (3 * core * ∑ i, pderiv i (L i)) = 0 := by
      have hassoc : 3 * core * ∑ i, pderiv i (L i) =
          3 * (core * ∑ i, pderiv i (L i)) := (mul_assoc _ _ _)
      rw [hassoc, coeff_three_mul, coeff_m_div_term L hL, mul_zero]
    rw [h2p, h2d, h3]
    simp
  rw [hval] at hcoeff
  exact two_ne_zero (α := ℂ) hcoeff

end
