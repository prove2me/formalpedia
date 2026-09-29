-- Prove2me | solution 1 for LassoDantzig.REConditions.assumption5_implies_RE
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T01:30:05.074908+00:00
-- url     : https://prove2.me/submissions/de183e13-0bb5-45bc-9c16-94dddb5d9bf2

import Mathlib
import Definitions.Def_LassoDantzig_REConditions_RE
import Definitions.Def_LassoDantzig_REConditions_RestrictedEigenvalues

namespace LassoDantzig.REConditions

/-- Entry `(j,k)` of the Gram matrix `Ψ_n = XᵀX/n`. -/
noncomputable def aux_a5_Psi {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ) (j k : Fin M) : ℝ :=
  (1 / (n : ℝ)) * ∑ i, X i j * X i k

theorem aux_a5_bilin {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ) (x y : Fin M → ℝ) :
    (1 / (n : ℝ)) * ∑ i, X.mulVec x i * X.mulVec y i =
      ∑ j, ∑ k, x j * y k * aux_a5_Psi X j k := by
  simp only [Matrix.mulVec, dotProduct, aux_a5_Psi]
  simp_rw [Finset.sum_mul_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem aux_a5_bdd {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ) (hn : 0 < n) (m1 m2 : ℕ) :
    BddAbove (corrSet X m1 m2) := by
  refine ⟨(∑ i, (∑ j, |X i j|) ^ 2) / n, ?_⟩
  rintro t ⟨I1, I2, -, -, -, c1, c2, -, -, hc1, hc2, rfl⟩
  have hpos : ∀ c : Fin M → ℝ, c ≠ 0 → 0 < ∑ j, c j ^ 2 := by
    intro c hc
    obtain ⟨j, hj⟩ := Function.ne_iff.1 hc
    exact Finset.sum_pos' (fun l _ => sq_nonneg _)
      ⟨j, Finset.mem_univ _, lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hj))⟩
  have hrow : ∀ c : Fin M → ℝ, ∀ i, |X.mulVec c i| ≤ (∑ j, |X i j|) * Real.sqrt (∑ j, c j ^ 2) := by
    intro c i
    have h1 : |X.mulVec c i| ≤ ∑ j, |X i j| * |c j| := by
      simp only [Matrix.mulVec, dotProduct]
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      simp [abs_mul]
    refine h1.trans ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun j _ => ?_
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    apply Real.abs_le_sqrt
    exact Finset.single_le_sum (f := fun l => c l ^ 2) (fun l _ => sq_nonneg _) (Finset.mem_univ j)
  have hS1 := hpos c1 hc1
  have hS2 := hpos c2 hc2
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hD : 0 < (n : ℝ) * Real.sqrt (∑ j, c1 j ^ 2) * Real.sqrt (∑ j, c2 j ^ 2) := by
    positivity
  rw [div_le_iff₀ hD]
  have hN : ∑ i, X.mulVec c1 i * X.mulVec c2 i ≤
      (∑ i, (∑ j, |X i j|) ^ 2) * Real.sqrt (∑ j, c1 j ^ 2) * Real.sqrt (∑ j, c2 j ^ 2) := by
    rw [Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_le_sum fun i _ => ?_
    calc X.mulVec c1 i * X.mulVec c2 i ≤ |X.mulVec c1 i| * |X.mulVec c2 i| := by
          rw [← abs_mul]; exact le_abs_self _
      _ ≤ ((∑ j, |X i j|) * Real.sqrt (∑ j, c1 j ^ 2)) *
            ((∑ j, |X i j|) * Real.sqrt (∑ j, c2 j ^ 2)) :=
          mul_le_mul (hrow c1 i) (hrow c2 i) (abs_nonneg _) (by positivity)
      _ = _ := by ring
  refine hN.trans (le_of_eq ?_)
  field_simp

theorem aux_a5_mem {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ) (j k : Fin M) (hjk : j ≠ k)
    (b : ℝ) (hb : b = 1 ∨ b = -1) :
    b * aux_a5_Psi X j k ∈ corrSet X 1 1 := by
  refine ⟨{j}, {k}, Finset.disjoint_singleton.2 hjk, by simp, by simp,
    Pi.single j 1, Pi.single k b, ?_, ?_, ?_, ?_, ?_⟩
  · intro l hl
    simp only [Finset.mem_singleton] at hl
    simp [hl]
  · intro l hl
    simp only [Finset.mem_singleton] at hl
    simp [hl]
  · intro h
    have := congrFun h j
    simp at this
  · intro h
    have := congrFun h k
    rcases hb with rfl | rfl <;> simp at this
  · have e1 : ∀ (l : Fin M) (a : ℝ), ∑ j', (Pi.single l a : Fin M → ℝ) j' ^ 2 = a ^ 2 := by
      intro l a
      rw [Finset.sum_eq_single l]
      · simp
      · intro j' _ hj'
        simp [hj']
      · simp
    rw [e1, e1]
    simp only [Matrix.mulVec_single, aux_a5_Psi]
    rcases hb with rfl | rfl
    · simp
      ring
    · simp
      ring

theorem aux_a5_Psi_le {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ) (hn : 0 < n)
    (j k : Fin M) (hjk : j ≠ k) :
    |aux_a5_Psi X j k| ≤ theta X 1 1 := by
  rw [abs_le]
  constructor
  · have := le_csSup (aux_a5_bdd X hn 1 1) (aux_a5_mem X j k hjk (-1) (Or.inr rfl))
    unfold theta
    linarith
  · have := le_csSup (aux_a5_bdd X hn 1 1) (aux_a5_mem X j k hjk 1 (Or.inl rfl))
    unfold theta
    linarith

theorem aux_a5_theta_nonneg {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ) (hn : 0 < n)
    (hM : 2 ≤ M) : 0 ≤ theta X 1 1 := by
  have h := aux_a5_Psi_le X hn ⟨0, by omega⟩ ⟨1, by omega⟩ (by simp [Fin.ext_iff])
  exact (abs_nonneg _).trans h

theorem aux_a5_term {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ) (hn : 0 < n) (hM : 2 ≤ M)
    (hdiag : ∀ j : Fin M, (1 / (n : ℝ)) * ∑ i, X i j ^ 2 = 1)
    (x y : Fin M → ℝ) (j k : Fin M) :
    (if j = k then x j * y j else 0) - theta X 1 1 * (|x j| * |y k|) ≤
      x j * y k * aux_a5_Psi X j k := by
  have hθ := aux_a5_theta_nonneg X hn hM
  by_cases hjk : j = k
  · subst hjk
    have hP : aux_a5_Psi X j j = 1 := by
      rw [← hdiag j, aux_a5_Psi]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    rw [if_pos rfl, hP, mul_one]
    have : 0 ≤ theta X 1 1 * (|x j| * |y j|) := by positivity
    linarith
  · rw [if_neg hjk, zero_sub]
    have h1 := aux_a5_Psi_le X hn j k hjk
    have h2 : |x j * y k * aux_a5_Psi X j k| ≤ theta X 1 1 * (|x j| * |y k|) := by
      rw [abs_mul, abs_mul]
      have : 0 ≤ |x j| * |y k| := by positivity
      nlinarith [abs_nonneg (aux_a5_Psi X j k)]
    have := neg_abs_le (x j * y k * aux_a5_Psi X j k)
    linarith

theorem aux_a5_bilin_ge {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ) (hn : 0 < n) (hM : 2 ≤ M)
    (hdiag : ∀ j : Fin M, (1 / (n : ℝ)) * ∑ i, X i j ^ 2 = 1)
    (x y : Fin M → ℝ) :
    ∑ j, x j * y j - theta X 1 1 * ((∑ j, |x j|) * (∑ k, |y k|)) ≤
      (1 / (n : ℝ)) * ∑ i, X.mulVec x i * X.mulVec y i := by
  rw [aux_a5_bilin]
  have h := Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) =>
    Finset.sum_le_sum fun k (_ : k ∈ Finset.univ) => aux_a5_term X hn hM hdiag x y j k
  refine le_trans (le_of_eq ?_) h
  simp only [Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [Finset.sum_mul_sum, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum]

theorem aux_a5_restrict_l1 {M : ℕ} (δ : Fin M → ℝ) (J : Finset (Fin M)) :
    ∑ j, |restrict δ J j| = l1On δ J := by
  simp only [restrict, l1On, apply_ite abs, abs_zero]
  rw [Finset.sum_ite_mem, Finset.univ_inter]

theorem aux_a5_restrict_l2 {M : ℕ} (δ : Fin M → ℝ) (J : Finset (Fin M)) :
    ∑ j, restrict δ J j * restrict δ J j = l2On δ J ^ 2 := by
  rw [l2On, Real.sq_sqrt (Finset.sum_nonneg fun j _ => sq_nonneg _)]
  simp only [restrict]
  have e : ∀ j, (if j ∈ J then δ j else 0) * (if j ∈ J then δ j else 0) =
      if j ∈ J then δ j ^ 2 else 0 := by
    intro j; split_ifs <;> ring
  simp only [e]
  rw [Finset.sum_ite_mem, Finset.univ_inter]

theorem aux_a5_l1_sq {M : ℕ} (δ : Fin M → ℝ) (J : Finset (Fin M)) (s : ℕ) (hJ : J.card ≤ s) :
    l1On δ J ^ 2 ≤ s * l2On δ J ^ 2 := by
  rw [l2On, Real.sq_sqrt (Finset.sum_nonneg fun j _ => sq_nonneg _), l1On]
  refine (sq_sum_le_card_mul_sum_sq).trans ?_
  have hcard : (J.card : ℝ) ≤ s := by exact_mod_cast hJ
  simp only [sq_abs]
  exact mul_le_mul_of_nonneg_right hcard (Finset.sum_nonneg fun j _ => sq_nonneg _)

theorem aux_a5_gram_eq {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ) (x : Fin M → ℝ) :
    gramQuad X x = (1 / (n : ℝ)) * ∑ i, X.mulVec x i * X.mulVec x i := by
  rw [gramQuad]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

end LassoDantzig.REConditions

open LassoDantzig.REConditions

theorem solution {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ)
    (hn : 1 ≤ n) (hM : 2 ≤ M)
    (hdiag : ∀ j : Fin M, (1 / (n : ℝ)) * ∑ i, X i j ^ 2 = 1)
    (s : ℕ) (c0 : ℝ) (hs : 1 ≤ s) (hsM : s ≤ M) (hc0 : 0 < c0)
    (hA5 : theta X 1 1 < 1 / ((1 + 2 * c0) * s)) :
    (∀ J0 : Finset (Fin M), J0.card ≤ s → ∀ δ : Fin M → ℝ,
      l2On δ J0 ^ 2 - theta X 1 1 * l1On δ J0 ^ 2 ≤ gramQuad X (restrict δ J0) ∧
      l2On δ J0 ^ 2 * (1 - theta X 1 1 * s) ≤ l2On δ J0 ^ 2 - theta X 1 1 * l1On δ J0 ^ 2) ∧
    0 < Real.sqrt (1 - (1 + 2 * c0) * theta X 1 1 * s) ∧
    RE X s c0 (Real.sqrt (1 - (1 + 2 * c0) * theta X 1 1 * s)) := by
  have hn0 : 0 < n := hn
  have hθ := aux_a5_theta_nonneg X hn0 hM
  have hs' : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have hK : 0 < 1 - (1 + 2 * c0) * theta X 1 1 * s := by
    have hpos : 0 < (1 + 2 * c0) * (s : ℝ) := by positivity
    rw [lt_div_iff₀ hpos] at hA5
    linarith
  -- core lower bound for the restricted vector
  have hcore : ∀ J0 : Finset (Fin M), ∀ δ : Fin M → ℝ,
      l2On δ J0 ^ 2 - theta X 1 1 * l1On δ J0 ^ 2 ≤ gramQuad X (restrict δ J0) := by
    intro J0 δ
    have h := aux_a5_bilin_ge X hn0 hM hdiag (restrict δ J0) (restrict δ J0)
    rw [aux_a5_restrict_l2, aux_a5_restrict_l1] at h
    rw [aux_a5_gram_eq]
    nlinarith
  refine ⟨?_, Real.sqrt_pos.2 hK, ?_⟩
  · intro J0 hJ0 δ
    refine ⟨hcore J0 δ, ?_⟩
    have := aux_a5_l1_sq δ J0 s hJ0
    nlinarith
  · intro J0 hJ0 δ _ hcone
    set u := restrict δ J0 with hu
    set v := restrict δ J0ᶜ with hv
    have hδ : δ = u + v := by
      funext j
      simp only [hu, hv, restrict, Pi.add_apply, Finset.mem_compl]
      split_ifs <;> simp
    have huv : ∑ j, u j * v j = 0 := by
      refine Finset.sum_eq_zero fun j _ => ?_
      simp only [hu, hv, restrict, Finset.mem_compl]
      split_ifs <;> simp
    have hB := aux_a5_bilin_ge X hn0 hM hdiag u v
    rw [huv, aux_a5_restrict_l1, aux_a5_restrict_l1] at hB
    have hA := hcore J0 δ
    rw [aux_a5_gram_eq] at hA
    have hl1 := aux_a5_l1_sq δ J0 s hJ0
    have hl1nn : 0 ≤ l1On δ J0 := Finset.sum_nonneg fun j _ => abs_nonneg _
    have hcone' : l1On δ J0ᶜ ≤ c0 * l1On δ J0 := hcone
    -- gramQuad of δ
    have hG : (1 / (n : ℝ)) * ∑ i, X.mulVec u i * X.mulVec u i +
        2 * ((1 / (n : ℝ)) * ∑ i, X.mulVec u i * X.mulVec v i) ≤
        (1 / (n : ℝ)) * ∑ i, X.mulVec δ i ^ 2 := by
      rw [hδ, Matrix.mulVec_add]
      have hn' : (0 : ℝ) < n := by exact_mod_cast hn0
      rw [mul_comm 2, mul_assoc, ← mul_add, Finset.sum_mul, ← Finset.sum_add_distrib]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      refine Finset.sum_le_sum fun i _ => ?_
      simp only [Pi.add_apply]
      nlinarith [sq_nonneg (X.mulVec v i)]
    have hmain : (1 - (1 + 2 * c0) * theta X 1 1 * s) * l2On δ J0 ^ 2 ≤
        (1 / (n : ℝ)) * ∑ i, X.mulVec δ i ^ 2 := by
      have h1 : theta X 1 1 * (l1On δ J0 * l1On δ J0ᶜ) ≤
          theta X 1 1 * (c0 * l1On δ J0 ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ hθ
        nlinarith
      have h2 : (1 + 2 * c0) * theta X 1 1 * l1On δ J0 ^ 2 ≤
          (1 + 2 * c0) * theta X 1 1 * (s * l2On δ J0 ^ 2) := by
        apply mul_le_mul_of_nonneg_left hl1
        positivity
      nlinarith
    -- conclude
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn0
    have hl2nn : 0 ≤ l2On δ J0 := Real.sqrt_nonneg _
    unfold euclNorm
    rw [show Real.sqrt (1 - (1 + 2 * c0) * theta X 1 1 * s) * Real.sqrt n * l2On δ J0 =
        Real.sqrt ((1 - (1 + 2 * c0) * theta X 1 1 * s) * n * l2On δ J0 ^ 2) by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_mul hK.le, Real.sqrt_sq hl2nn]]
    apply Real.sqrt_le_sqrt
    have := mul_le_mul_of_nonneg_left hmain hn'.le
    have e : (n : ℝ) * (1 / (n : ℝ) * ∑ i, X.mulVec δ i ^ 2) = ∑ i, X.mulVec δ i ^ 2 := by
      field_simp
    rw [e] at this
    linarith
