-- Prove2me | solution 1 for LassoDantzig.Lasso.eq_B30_B31
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T03:14:03.141989+00:00
-- url     : https://prove2.me/submissions/20889a5d-79b7-4e72-b4cc-f51ee970abdf

import Mathlib
import Definitions.Def_LassoDantzig_Lasso_Model

open MeasureTheory ProbabilityTheory

namespace LassoDantzig.Lasso

theorem aux_b3031_l1split {M : ℕ} (δ : Fin M → ℝ) (J : Finset (Fin M)) :
    l1Norm δ = l1On δ J + l1On δ Jᶜ := by
  unfold l1Norm l1On
  rw [Finset.sum_add_sum_compl]

theorem aux_b3031_l1On_nonneg {M : ℕ} (δ : Fin M → ℝ) (J : Finset (Fin M)) :
    0 ≤ l1On δ J := Finset.sum_nonneg (fun _ _ => abs_nonneg _)

theorem aux_b3031_cs {M : ℕ} (δ : Fin M → ℝ) (J : Finset (Fin M)) (s : ℕ) (hJ : J.card ≤ s) :
    l1On δ J ≤ Real.sqrt s * l2On δ J := by
  unfold l2On
  rw [← Real.sqrt_mul (Nat.cast_nonneg _)]
  have h4 : 0 ≤ ∑ j ∈ J, δ j ^ 2 := Finset.sum_nonneg (fun j _ => sq_nonneg _)
  rw [Real.le_sqrt (aux_b3031_l1On_nonneg δ J) (by positivity)]
  have h1 : (∑ j ∈ J, |δ j|) ^ 2 ≤ J.card * ∑ j ∈ J, |δ j| ^ 2 := sq_sum_le_card_mul_sum_sq
  have h2 : ∑ j ∈ J, |δ j| ^ 2 = ∑ j ∈ J, δ j ^ 2 := by simp [sq_abs]
  have h3 : (J.card : ℝ) ≤ s := by exact_mod_cast hJ
  unfold l1On
  rw [h2] at h1
  nlinarith

theorem aux_b3031_cross {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ) (w : Fin n → ℝ)
    (δ : Fin M → ℝ) :
    (1 / (n : ℝ)) * ∑ i, w i * X.mulVec δ i =
      ∑ j, δ j * ((1 / (n : ℝ)) * ∑ i, X i j * w i) := by
  simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem aux_b3031_noise {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ) (r : ℝ) (w : Fin n → ℝ)
    (hw : NoiseEventHalf X r w) (δ : Fin M → ℝ) :
    2 * ((1 / (n : ℝ)) * ∑ i, w i * X.mulVec δ i) ≤ r * l1Norm δ := by
  rw [aux_b3031_cross, Finset.mul_sum]
  unfold l1Norm
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  have h := hw j
  set V := (1 / (n : ℝ)) * ∑ i, X i j * w i
  have e1 : 2 * (δ j * V) ≤ |δ j| * (2 * |V|) := by
    rw [show 2 * (δ j * V) = δ j * (2 * V) by ring]
    calc δ j * (2 * V) ≤ |δ j * (2 * V)| := le_abs_self _
      _ = |δ j| * (2 * |V|) := by rw [abs_mul, abs_mul, abs_two]
  have e2 : |δ j| * (2 * |V|) ≤ |δ j| * r := mul_le_mul_of_nonneg_left h (abs_nonneg _)
  linarith

theorem aux_b3031_l1diff {M : ℕ} (βhat βstar : Fin M → ℝ) :
    l1Norm (βhat - βstar) + l1Norm βstar - l1Norm βhat ≤
      2 * l1On (βhat - βstar) (supp βstar) := by
  have hs1 := aux_b3031_l1split (βhat - βstar) (supp βstar)
  have hs2 := aux_b3031_l1split βstar (supp βstar)
  have hs3 := aux_b3031_l1split βhat (supp βstar)
  have hc : ∀ j ∈ (supp βstar)ᶜ, βstar j = 0 := by
    intro j hj
    simpa [supp] using hj
  have e1 : l1On (βhat - βstar) (supp βstar)ᶜ = l1On βhat (supp βstar)ᶜ :=
    Finset.sum_congr rfl (fun j hj => by simp [hc j hj])
  have e2 : l1On βstar (supp βstar)ᶜ = 0 :=
    Finset.sum_eq_zero (fun j hj => by simp [hc j hj])
  have e3 : l1On βstar (supp βstar) ≤ l1On (βhat - βstar) (supp βstar) + l1On βhat (supp βstar) := by
    unfold l1On
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro j _
    simp only [Pi.sub_apply]
    have := abs_sub_abs_le_abs_sub (βstar j) (βhat j)
    rw [abs_sub_comm] at this
    linarith
  linarith

end LassoDantzig.Lasso

open MeasureTheory ProbabilityTheory
open LassoDantzig.Lasso

theorem solution {n M : ℕ} (hn : 1 ≤ n) (hM : 2 ≤ M)
    (X : Matrix (Fin n) (Fin M) ℝ) (hX : UnitDiag X) (βstar : Fin M → ℝ)
    (s : ℕ) (hs1 : 1 ≤ s) (hsM : s ≤ M) (hsparse : sparsity βstar ≤ s)
    (κ : ℝ) (hκ : 0 < κ) (hRE : RE X s 3 κ)
    (r : ℝ) (hr : 0 < r) (w : Fin n → ℝ) (hw : NoiseEventHalf X r w)
    (βhat : Fin M → ℝ) (hL : IsLasso X (fun i => X.mulVec βstar i + w i) r βhat) :
    (1 / (n : ℝ)) * ∑ i, (X.mulVec (βhat - βstar) i) ^ 2 ≤
        4 * r * Real.sqrt s * l2On (βhat - βstar) (supp βstar) ∧
      ConeCond 3 (supp βstar) (βhat - βstar) ∧
      (1 / (n : ℝ)) * ∑ i, (X.mulVec (βhat - βstar) i) ^ 2 ≤ 16 * r ^ 2 * s / κ ^ 2 ∧
      l2On (βhat - βstar) (supp βstar) ≤ 4 * r * Real.sqrt s / κ ^ 2 := by
  have hno := aux_b3031_noise X r w hw (βhat - βstar)
  have hl1 := aux_b3031_l1diff βhat βstar
  have hsplit := aux_b3031_l1split (βhat - βstar) (supp βstar)
  have hJ0 := aux_b3031_l1On_nonneg (βhat - βstar) (supp βstar)
  have hJc0 := aux_b3031_l1On_nonneg (βhat - βstar) (supp βstar)ᶜ
  have hcard : (supp βstar).card ≤ s := hsparse
  have hcs := aux_b3031_cs (βhat - βstar) (supp βstar) s hcard
  have hu : ∀ i, X.mulVec (βhat - βstar) i = X.mulVec βhat i - X.mulVec βstar i := by
    intro i; simp [Matrix.mulVec_sub]
  have h1 := hL βstar
  simp only at h1
  have hsum1 : ∑ i, (X.mulVec βstar i + w i - X.mulVec βhat i) ^ 2 =
      ∑ i, w i ^ 2 - 2 * ∑ i, w i * X.mulVec (βhat - βstar) i +
        ∑ i, (X.mulVec (βhat - βstar) i) ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [hu]
    ring
  have hsum2 : ∑ i, (X.mulVec βstar i + w i - X.mulVec βstar i) ^ 2 = ∑ i, w i ^ 2 := by
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hsum1, hsum2] at h1
  set δ := βhat - βstar with hδ
  set J := supp βstar with hJ
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hinv : (0 : ℝ) < 1 / (n : ℝ) := by positivity
  set Su := ∑ i, (X.mulVec δ i) ^ 2 with hSu
  set C := ∑ i, w i * X.mulVec δ i with hC
  set Sw := ∑ i, w i ^ 2 with hSw
  set A := (1 / (n : ℝ)) * Su with hA
  have hSu0 : 0 ≤ Su := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hA0 : 0 ≤ A := mul_nonneg hinv.le hSu0
  have hexp : (1 / (n : ℝ)) * (Sw - 2 * C + Su) = (1 / (n : ℝ)) * Sw - 2 * ((1 / (n : ℝ)) * C) + A := by
    rw [hA]; ring
  rw [hexp] at h1
  have hl1' := mul_le_mul_of_nonneg_left hl1 (by positivity : (0 : ℝ) ≤ 2 * r)
  have key : A + r * l1Norm δ ≤ 4 * r * l1On δ J := by
    nlinarith
  have cone : ConeCond 3 J δ := by
    unfold ConeCond
    have : r * l1On δ Jᶜ ≤ r * (3 * l1On δ J) := by
      rw [hsplit] at key
      nlinarith
    exact le_of_mul_le_mul_left this hr
  have b30 : A ≤ 4 * r * Real.sqrt s * l2On δ J := by
    have e1 : r * l1On δ J ≤ r * (Real.sqrt s * l2On δ J) := mul_le_mul_of_nonneg_left hcs hr.le
    have e2 : 0 ≤ r * l1Norm δ := mul_nonneg hr.le (by rw [hsplit]; linarith)
    nlinarith
  have hL0 : 0 ≤ l2On δ J := Real.sqrt_nonneg _
  have hRE' : κ ^ 2 * l2On δ J ^ 2 ≤ A := by
    by_cases hδ0 : δ = 0
    · have : l2On δ J = 0 := by simp [hδ0, l2On]
      rw [this]
      simpa using hA0
    · have h := hRE J hcard δ hδ0 cone
      unfold euclNorm at h
      have hnn : 0 ≤ κ * Real.sqrt n * l2On δ J := by positivity
      have h2 : (κ * Real.sqrt n * l2On δ J) ^ 2 ≤ Su := by
        calc (κ * Real.sqrt n * l2On δ J) ^ 2 ≤ (Real.sqrt Su) ^ 2 := pow_le_pow_left₀ hnn h 2
          _ = Su := Real.sq_sqrt hSu0
      have h3 : (κ * Real.sqrt n * l2On δ J) ^ 2 = κ ^ 2 * l2On δ J ^ 2 * n := by
        rw [mul_pow, mul_pow, Real.sq_sqrt hnpos.le]
        ring
      rw [h3] at h2
      rw [hA, div_mul_eq_mul_div, one_mul, le_div_iff₀ hnpos]
      exact h2
  have b31b : l2On δ J ≤ 4 * r * Real.sqrt s / κ ^ 2 := by
    rw [le_div_iff₀ (by positivity)]
    rcases hL0.eq_or_lt with h0 | hpos
    · rw [← h0]
      simp only [zero_mul]
      positivity
    · have : κ ^ 2 * l2On δ J ^ 2 ≤ 4 * r * Real.sqrt s * l2On δ J := le_trans hRE' b30
      nlinarith
  have hss : Real.sqrt s * Real.sqrt s = s := Real.mul_self_sqrt (Nat.cast_nonneg _)
  have b31a : A ≤ 16 * r ^ 2 * s / κ ^ 2 := by
    calc A ≤ 4 * r * Real.sqrt s * l2On δ J := b30
      _ ≤ 4 * r * Real.sqrt s * (4 * r * Real.sqrt s / κ ^ 2) :=
          mul_le_mul_of_nonneg_left b31b (by positivity)
      _ = 16 * r ^ 2 * (Real.sqrt s * Real.sqrt s) / κ ^ 2 := by ring
      _ = 16 * r ^ 2 * s / κ ^ 2 := by rw [hss]
  exact ⟨b30, cone, b31a, b31b⟩
