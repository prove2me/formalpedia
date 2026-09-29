-- Prove2me | solution 1 for LassoDantzig.REConditions.assumption4_implies_RE
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T00:42:17.710869+00:00
-- url     : https://prove2.me/submissions/ae5841fc-f071-4be6-af00-123cbc42cf30

import Mathlib
import Definitions.Def_LassoDantzig_REConditions_RE
import Definitions.Def_LassoDantzig_REConditions_RestrictedEigenvalues

namespace LassoDantzig.REConditions

theorem aux_a4re_mulVec_abs {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ) (c : Fin M → ℝ)
    (i : Fin n) :
    |X.mulVec c i| ≤ (∑ j, |X i j|) * Real.sqrt (∑ j, c j ^ 2) := by
  have hc : ∀ j, |c j| ≤ Real.sqrt (∑ l, c l ^ 2) := fun j =>
    Real.abs_le_sqrt (Finset.single_le_sum (f := fun l => c l ^ 2)
      (fun l _ => sq_nonneg (c l)) (Finset.mem_univ j))
  calc |X.mulVec c i| = |∑ j, X i j * c j| := rfl
    _ ≤ ∑ j, |X i j * c j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, |X i j| * Real.sqrt (∑ l, c l ^ 2) := by
        apply Finset.sum_le_sum; intro j _; rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hc j) (abs_nonneg _)
    _ = (∑ j, |X i j|) * Real.sqrt (∑ j, c j ^ 2) := by rw [Finset.sum_mul]

theorem aux_a4re_sqrt_pos {M : ℕ} (c : Fin M → ℝ) (hc : c ≠ 0) :
    0 < ∑ j, c j ^ 2 := by
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hc
  exact lt_of_lt_of_le (lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hj)))
    (Finset.single_le_sum (f := fun l => c l ^ 2) (fun l _ => sq_nonneg (c l))
      (Finset.mem_univ j))

theorem aux_a4re_corr_bdd {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ) (hn : 1 ≤ n)
    (m1 m2 : ℕ) : BddAbove (corrSet X m1 m2) := by
  refine ⟨(∑ i, (∑ j, |X i j|) ^ 2) / n, ?_⟩
  rintro t ⟨I1, I2, -, -, -, c1, c2, -, -, hc1, hc2, rfl⟩
  have hnpos : (0:ℝ) < n := by exact_mod_cast hn
  have hA : 0 < Real.sqrt (∑ j, c1 j ^ 2) := Real.sqrt_pos.mpr (aux_a4re_sqrt_pos c1 hc1)
  have hB : 0 < Real.sqrt (∑ j, c2 j ^ 2) := Real.sqrt_pos.mpr (aux_a4re_sqrt_pos c2 hc2)
  have hS : |∑ i, X.mulVec c1 i * X.mulVec c2 i| ≤
      (∑ i, (∑ j, |X i j|) ^ 2) * Real.sqrt (∑ j, c1 j ^ 2) * Real.sqrt (∑ j, c2 j ^ 2) := by
    calc |∑ i, X.mulVec c1 i * X.mulVec c2 i|
        ≤ ∑ i, |X.mulVec c1 i * X.mulVec c2 i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, ((∑ j, |X i j|) * Real.sqrt (∑ j, c1 j ^ 2)) *
            ((∑ j, |X i j|) * Real.sqrt (∑ j, c2 j ^ 2)) := by
        apply Finset.sum_le_sum; intro i _; rw [abs_mul]
        exact mul_le_mul (aux_a4re_mulVec_abs X c1 i) (aux_a4re_mulVec_abs X c2 i)
          (abs_nonneg _) (mul_nonneg (Finset.sum_nonneg fun j _ => abs_nonneg _) hA.le)
      _ = (∑ i, (∑ j, |X i j|) ^ 2) * Real.sqrt (∑ j, c1 j ^ 2) *
            Real.sqrt (∑ j, c2 j ^ 2) := by
        rw [Finset.sum_mul, Finset.sum_mul]; apply Finset.sum_congr rfl; intro i _; ring
  rw [div_le_div_iff₀ (by positivity) hnpos]
  calc (∑ i, X.mulVec c1 i * X.mulVec c2 i) * n
      ≤ ((∑ i, (∑ j, |X i j|) ^ 2) * Real.sqrt (∑ j, c1 j ^ 2) *
          Real.sqrt (∑ j, c2 j ^ 2)) * n :=
        mul_le_mul_of_nonneg_right (le_trans (le_abs_self _) hS) hnpos.le
    _ = (∑ i, (∑ j, |X i j|) ^ 2) *
          (n * Real.sqrt (∑ j, c1 j ^ 2) * Real.sqrt (∑ j, c2 j ^ 2)) := by ring

theorem aux_a4re_pair {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ) (hn : 1 ≤ n) (j k : Fin M)
    (hjk : j ≠ k) (x y : ℝ) (hx : x ≠ 0) (hy : y ≠ 0) :
    x * y * (∑ i, X i j * X i k) ≤ theta X 1 1 * n * |x| * |y| := by
  have hnpos : (0:ℝ) < n := by exact_mod_cast hn
  have hmem : (∑ i, X.mulVec (Pi.single j x) i * X.mulVec (Pi.single k y) i) /
      ((n : ℝ) * Real.sqrt (∑ l, (Pi.single j x : Fin M → ℝ) l ^ 2) *
        Real.sqrt (∑ l, (Pi.single k y : Fin M → ℝ) l ^ 2)) ∈ corrSet X 1 1 := by
    refine ⟨{j}, {k}, Finset.disjoint_singleton.mpr hjk, by simp, by simp,
      Pi.single j x, Pi.single k y, ?_, ?_, ?_, ?_, rfl⟩
    · intro l hl; simp at hl; simp [hl]
    · intro l hl; simp at hl; simp [hl]
    · intro h; have := congrFun h j; simp at this; exact hx this
    · intro h; have := congrFun h k; simp at this; exact hy this
  have hle := le_csSup (aux_a4re_corr_bdd X hn 1 1) hmem
  have h1 : ∀ (l : Fin M) (z : ℝ), X.mulVec (Pi.single l z) = fun i => X i l * z := by
    intro l z; ext i; exact dotProduct_single _ _ _
  have h2 : ∀ (l : Fin M) (z : ℝ), ∑ m, (Pi.single l z : Fin M → ℝ) m ^ 2 = z ^ 2 := by
    intro l z
    rw [Fintype.sum_eq_single l]
    · simp
    intro m hm; simp [hm]
  rw [h1, h1, h2, h2, Real.sqrt_sq_eq_abs, Real.sqrt_sq_eq_abs] at hle
  have hpos : 0 < (n:ℝ) * |x| * |y| := by positivity
  rw [div_le_iff₀ hpos] at hle
  unfold theta
  calc x * y * (∑ i, X i j * X i k) = ∑ i, X i j * x * (X i k * y) := by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring
    _ ≤ _ := hle
    _ = _ := by ring

theorem aux_a4re_theta_nonneg {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ) (hn : 1 ≤ n)
    (hM : 2 ≤ M) : 0 ≤ theta X 1 1 := by
  have hnpos : (0:ℝ) < n := by exact_mod_cast hn
  have hjk : (⟨0, by omega⟩ : Fin M) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
  have h1 := aux_a4re_pair X hn _ _ hjk 1 1 one_ne_zero one_ne_zero
  have h2 := aux_a4re_pair X hn _ _ hjk 1 (-1) one_ne_zero (by norm_num)
  simp at h1 h2
  nlinarith

theorem aux_a4re_restrict_sq {M : ℕ} (δ : Fin M → ℝ) (J : Finset (Fin M)) :
    ∑ j, restrict δ J j ^ 2 = ∑ j ∈ J, δ j ^ 2 := by
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun j => j ∈ J)]
  have h1 : ∑ j ∈ Finset.univ.filter (fun j => j ∈ J), restrict δ J j ^ 2 = ∑ j ∈ J, δ j ^ 2 := by
    rw [Finset.filter_mem_eq_inter, Finset.univ_inter]
    apply Finset.sum_congr rfl; intro j hj; simp [restrict, hj]
  have h2 : ∑ j ∈ Finset.univ.filter (fun j => j ∉ J), restrict δ J j ^ 2 = 0 := by
    apply Finset.sum_eq_zero; intro j hj; simp at hj; simp [restrict, hj]
  rw [h1, h2, add_zero]

theorem aux_a4re_restrict_abs {M : ℕ} (δ : Fin M → ℝ) (J : Finset (Fin M)) :
    ∑ j, |restrict δ J j| = l1On δ J := by
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun j => j ∈ J)]
  have h1 : ∑ j ∈ Finset.univ.filter (fun j => j ∈ J), |restrict δ J j| = l1On δ J := by
    rw [Finset.filter_mem_eq_inter, Finset.univ_inter]
    apply Finset.sum_congr rfl; intro j hj; simp [restrict, hj]
  have h2 : ∑ j ∈ Finset.univ.filter (fun j => j ∉ J), |restrict δ J j| = 0 := by
    apply Finset.sum_eq_zero; intro j hj; simp at hj; simp [restrict, hj]
  rw [h1, h2, add_zero]

theorem aux_a4re_step1 {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ) (hn : 1 ≤ n)
    (J0 : Finset (Fin M)) (δ : Fin M → ℝ) :
    gramQuad X (restrict δ J0) - 2 * theta X 1 1 * l1On δ J0ᶜ * l1On δ J0 ≤ gramQuad X δ := by
  have hnpos : (0:ℝ) < n := by exact_mod_cast hn
  obtain ⟨a, ha⟩ : ∃ a, a = restrict δ J0 := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, b = restrict δ J0ᶜ := ⟨_, rfl⟩
  have hδ : δ = a + b := by
    funext j; by_cases hj : j ∈ J0 <;> simp [ha, hb, restrict, hj]
  have hl1a : l1On δ J0 = ∑ j, |a j| := by rw [ha, aux_a4re_restrict_abs]
  have hl1b : l1On δ J0ᶜ = ∑ j, |b j| := by rw [hb, aux_a4re_restrict_abs]
  have hterm : ∀ j k, -(theta X 1 1 * n * (|a j| * |b k|)) ≤
      a j * b k * (∑ i, X i j * X i k) := by
    intro j k
    by_cases haj : a j = 0
    · simp [haj]
    by_cases hbk : b k = 0
    · simp [hbk]
    have hj : j ∈ J0 := by
      by_contra h; exact haj (by simp [ha, restrict, h])
    have hk : k ∉ J0 := by
      intro h; exact hbk (by simp [hb, restrict, h])
    have hjk : j ≠ k := by rintro rfl; exact hk hj
    have := aux_a4re_pair X hn j k hjk (a j) (-(b k)) haj (neg_ne_zero.mpr hbk)
    rw [abs_neg] at this
    linarith
  have heq : ∑ i, X.mulVec a i * X.mulVec b i =
      ∑ j, ∑ k, a j * b k * (∑ i, X i j * X i k) := by
    have hi : ∀ i, X.mulVec a i * X.mulVec b i =
        ∑ j, ∑ k, a j * b k * (X i j * X i k) := by
      intro i
      show (∑ j, X i j * a j) * (∑ k, X i k * b k) = _
      rw [Finset.sum_mul_sum]
      apply Finset.sum_congr rfl; intro j _; apply Finset.sum_congr rfl; intro k _; ring
    calc ∑ i, X.mulVec a i * X.mulVec b i
        = ∑ i, ∑ j, ∑ k, a j * b k * (X i j * X i k) := by simp only [hi]
      _ = ∑ j, ∑ i, ∑ k, a j * b k * (X i j * X i k) := Finset.sum_comm
      _ = ∑ j, ∑ k, ∑ i, a j * b k * (X i j * X i k) :=
          Finset.sum_congr rfl (fun j _ => Finset.sum_comm)
      _ = _ := by simp only [Finset.mul_sum]
  have hcross : -(theta X 1 1 * n * ((∑ j, |a j|) * (∑ k, |b k|))) ≤
      ∑ i, X.mulVec a i * X.mulVec b i := by
    rw [heq]
    calc -(theta X 1 1 * n * ((∑ j, |a j|) * (∑ k, |b k|)))
        = ∑ j, ∑ k, -(theta X 1 1 * n * (|a j| * |b k|)) := by
          rw [Finset.sum_mul_sum, Finset.mul_sum, ← Finset.sum_neg_distrib]
          apply Finset.sum_congr rfl; intro j _
          rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
      _ ≤ _ := Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun k _ => hterm j k
  have hXδ : X.mulVec δ = X.mulVec a + X.mulVec b := by
    rw [← Matrix.mulVec_add, ← hδ]
  have hgram : gramQuad X δ = gramQuad X a +
      (2 / n) * (∑ i, X.mulVec a i * X.mulVec b i) + gramQuad X b := by
    unfold gramQuad
    rw [hXδ]
    simp only [Pi.add_apply, add_sq, Finset.sum_add_distrib]
    have hsum : ∑ x, 2 * X.mulVec a x * X.mulVec b x = 2 * ∑ x, X.mulVec a x * X.mulVec b x := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro x _; ring
    rw [hsum]
    ring
  have hb0 : 0 ≤ gramQuad X b := by unfold gramQuad; positivity
  have h2n : (2 / (n:ℝ)) * (-(theta X 1 1 * n * ((∑ j, |a j|) * (∑ k, |b k|)))) =
      -(2 * theta X 1 1 * (∑ k, |b k|) * (∑ j, |a j|)) := by
    field_simp
  have hmul := mul_le_mul_of_nonneg_left hcross (by positivity : (0:ℝ) ≤ 2 / n)
  rw [h2n] at hmul
  rw [hgram, hl1a, hl1b, ← ha]
  linarith

theorem aux_a4re_phimin {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ) (s : ℕ)
    (J0 : Finset (Fin M)) (hJ0 : J0.card ≤ s) (δ : Fin M → ℝ) :
    phiMin X s * ∑ j, restrict δ J0 j ^ 2 ≤ gramQuad X (restrict δ J0) := by
  by_cases h0 : restrict δ J0 = 0
  · rw [h0]; simp [gramQuad]
  · have hbdd : BddBelow (rayleighSet X s) := by
      refine ⟨0, ?_⟩
      rintro q ⟨x, -, -, rfl⟩
      unfold gramQuad; positivity
    have hpos : 0 < ∑ j, restrict δ J0 j ^ 2 := aux_a4re_sqrt_pos _ h0
    have hmem : gramQuad X (restrict δ J0) / ∑ j, restrict δ J0 j ^ 2 ∈ rayleighSet X s := by
      refine ⟨restrict δ J0, ?_, ?_, rfl⟩
      · obtain ⟨j, hj⟩ := Function.ne_iff.mp h0
        unfold sparsity supp
        exact Finset.card_pos.mpr ⟨j, by simpa using hj⟩
      · unfold sparsity supp
        refine le_trans (Finset.card_le_card ?_) hJ0
        intro j hj
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
        by_contra h
        exact hj (by simp [restrict, h])
    have := csInf_le hbdd hmem
    rw [le_div_iff₀ hpos] at this
    exact this

end LassoDantzig.REConditions

open LassoDantzig.REConditions

theorem solution {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ)
    (hn : 1 ≤ n) (hM : 2 ≤ M)
    (s : ℕ) (c0 : ℝ) (hs : 1 ≤ s) (hsM : s ≤ M) (hc0 : 0 < c0)
    (hA4 : 2 * c0 * theta X 1 1 * s < phiMin X s) :
    (∀ J0 : Finset (Fin M), J0.card ≤ s → ∀ δ : Fin M → ℝ, ConeCond c0 J0 δ →
      gramQuad X (restrict δ J0) - 2 * theta X 1 1 * l1On δ J0ᶜ * l1On δ J0 ≤ gramQuad X δ ∧
      phiMin X s * l2On δ J0 ^ 2 - 2 * c0 * theta X 1 1 * l1On δ J0 ^ 2 ≤
        gramQuad X (restrict δ J0) - 2 * theta X 1 1 * l1On δ J0ᶜ * l1On δ J0 ∧
      (phiMin X s - 2 * c0 * theta X 1 1 * s) * l2On δ J0 ^ 2 ≤
        phiMin X s * l2On δ J0 ^ 2 - 2 * c0 * theta X 1 1 * l1On δ J0 ^ 2) ∧
    0 < Real.sqrt (phiMin X s - 2 * c0 * theta X 1 1 * s) ∧
    RE X s c0 (Real.sqrt (phiMin X s - 2 * c0 * theta X 1 1 * s)) := by
  have hnpos : (0:ℝ) < n := by exact_mod_cast hn
  have hθ : 0 ≤ theta X 1 1 := aux_a4re_theta_nonneg X hn hM
  have hD : 0 < phiMin X s - 2 * c0 * theta X 1 1 * s := by linarith
  have hchain : ∀ J0 : Finset (Fin M), J0.card ≤ s → ∀ δ : Fin M → ℝ, ConeCond c0 J0 δ →
      gramQuad X (restrict δ J0) - 2 * theta X 1 1 * l1On δ J0ᶜ * l1On δ J0 ≤ gramQuad X δ ∧
      phiMin X s * l2On δ J0 ^ 2 - 2 * c0 * theta X 1 1 * l1On δ J0 ^ 2 ≤
        gramQuad X (restrict δ J0) - 2 * theta X 1 1 * l1On δ J0ᶜ * l1On δ J0 ∧
      (phiMin X s - 2 * c0 * theta X 1 1 * s) * l2On δ J0 ^ 2 ≤
        phiMin X s * l2On δ J0 ^ 2 - 2 * c0 * theta X 1 1 * l1On δ J0 ^ 2 := by
    intro J0 hJ0 δ hcone
    have hl2 : l2On δ J0 ^ 2 = ∑ j, restrict δ J0 j ^ 2 := by
      rw [aux_a4re_restrict_sq]; unfold l2On
      exact Real.sq_sqrt (Finset.sum_nonneg fun j _ => sq_nonneg _)
    have hL1a : 0 ≤ l1On δ J0 := Finset.sum_nonneg fun j _ => abs_nonneg _
    refine ⟨aux_a4re_step1 X hn J0 δ, ?_, ?_⟩
    · have h1 := aux_a4re_phimin X s J0 hJ0 δ
      rw [← hl2] at h1
      have h2 := mul_le_mul_of_nonneg_left (show l1On δ J0ᶜ ≤ c0 * l1On δ J0 from hcone)
        (mul_nonneg hθ hL1a)
      nlinarith
    · have hcs : l1On δ J0 ^ 2 ≤ (s : ℝ) * l2On δ J0 ^ 2 := by
        have h := sq_sum_le_card_mul_sum_sq (s := J0) (f := fun j => |δ j|)
        simp only [sq_abs] at h
        rw [hl2, aux_a4re_restrict_sq]
        unfold l1On
        refine le_trans h ?_
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hJ0)
          (Finset.sum_nonneg fun j _ => sq_nonneg _)
      have hc0θ : 0 ≤ c0 * theta X 1 1 := mul_nonneg hc0.le hθ
      nlinarith
  refine ⟨hchain, Real.sqrt_pos.mpr hD, ?_⟩
  intro J0 hJ0 δ _ hcone
  obtain ⟨h1, h2, h3⟩ := hchain J0 hJ0 δ hcone
  have hmain : (phiMin X s - 2 * c0 * theta X 1 1 * s) * l2On δ J0 ^ 2 ≤ gramQuad X δ := by
    linarith
  unfold gramQuad at hmain
  unfold euclNorm
  have hl2nn : 0 ≤ l2On δ J0 := Real.sqrt_nonneg _
  rw [Real.le_sqrt (by positivity) (Finset.sum_nonneg fun i _ => sq_nonneg _)]
  rw [mul_pow, mul_pow, Real.sq_sqrt hD.le, Real.sq_sqrt hnpos.le]
  have := mul_le_mul_of_nonneg_left hmain hnpos.le
  have e : (n:ℝ) * (1 / n * ∑ i, X.mulVec δ i ^ 2) = ∑ i, X.mulVec δ i ^ 2 := by
    field_simp
  rw [e] at this
  linarith
