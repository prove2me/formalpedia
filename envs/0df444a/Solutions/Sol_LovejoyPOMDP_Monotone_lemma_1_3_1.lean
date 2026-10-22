-- Prove2me | solution 1 for LovejoyPOMDP.Monotone.lemma_1_3_1
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T06:08:14.397731+00:00
-- url     : https://prove2.me/submissions/bce62313-60fc-485c-bcc3-5ade94b139da

import Mathlib
import Definitions.Def_LovejoyPOMDP_Monotone_Model

set_option autoImplicit false
open LovejoyPOMDP.Monotone

section lpm
variable {S O A : Type*} [Fintype S] [Fintype O] [Fintype A]

lemma lpm_predict_nonneg (M : POMDP S O A) {π : S → ℝ} (hπ : π ∈ stdSimplex ℝ S) (a : A) (j : S) :
    0 ≤ M.predict π a j := by
  unfold POMDP.predict
  exact Finset.sum_nonneg (fun i _ => mul_nonneg (hπ.1 i) ((M.P_row a i).1 j))

lemma lpm_sigma_nonneg (M : POMDP S O A) {π : S → ℝ} (hπ : π ∈ stdSimplex ℝ S) (a : A) (k : O) :
    0 ≤ M.sigma π a k := by
  unfold POMDP.sigma
  exact Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ =>
    mul_nonneg (mul_nonneg (hπ.1 i) ((M.P_row a i).1 j)) (M.R_pos a j k).le))

lemma lpm_bayes_eq (M : POMDP S O A) (π : S → ℝ) (a : A) (k : O) (j : S) :
    M.bayes π a k j = M.predict π a j * M.R a j k / M.sigma π a k := by
  unfold POMDP.bayes POMDP.predict
  rw [Finset.sum_mul]

lemma lpm_two_pt (A B C D a b c d : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (c1 : B * a ≤ A * b) (c2 : D * c ≤ C * d) (c5 : A * d ≤ C * b) (c6 : D * a ≤ C * b)
    (c7 : B * c ≤ C * b) : 0 ≤ A * d + C * b - B * c - D * a := by
  by_cases hCb : C * b = 0
  · have h1 : A * d = 0 := le_antisymm (by linarith) (mul_nonneg hA hd)
    have h2 : D * a = 0 := le_antisymm (by linarith) (mul_nonneg hD ha)
    have h3 : B * c = 0 := le_antisymm (by linarith) (mul_nonneg hB hc)
    linarith
  · have hpos : 0 < C * b := lt_of_le_of_ne (mul_nonneg hC hb) (Ne.symm hCb)
    have key : (A * d + C * b - B * c - D * a) * (C * b) =
        (A * b - B * a) * (C * d) + (C * d - D * c) * (B * a) + (C * b - D * a) * (C * b - B * c) := by
      ring
    have hrhs : 0 ≤ (A * b - B * a) * (C * d) + (C * d - D * c) * (B * a) +
        (C * b - D * a) * (C * b - B * c) := by
      have := mul_nonneg (sub_nonneg.2 c1) (mul_nonneg hC hd)
      have := mul_nonneg (sub_nonneg.2 c2) (mul_nonneg hB ha)
      have := mul_nonneg (sub_nonneg.2 c6) (sub_nonneg.2 c7)
      linarith
    by_contra hneg
    push_neg at hneg
    have := mul_neg_of_neg_of_pos hneg hpos
    linarith

lemma lpm_A_nonneg {S : Type*} [LinearOrder S] (f : S → S → ℝ) (h : TP2 f) (i i' j j' : S)
    (hii' : i' ≤ i) (hjj' : j' ≤ j) : 0 ≤ f i j * f i' j' - f i j' * f i' j := by
  have := h i' j i j'
  rw [max_eq_right hii', min_eq_left hii', max_eq_left hjj', min_eq_right hjj'] at this
  linarith

end lpm

theorem solution {S O A : Type*} [Fintype S] [Fintype O] [Fintype A]
    [LinearOrder S] [LinearOrder O] [LinearOrder A] [Nonempty S] [Nonempty O] [Nonempty A]
    (M : POMDP S O A)
    (hP : ∀ a, TP2 (M.P a)) (a : A) {π π' : S → ℝ}
    (hπ : π ∈ stdSimplex ℝ S) (hπ' : π' ∈ stdSimplex ℝ S) (h : MLRGE π π') :
    MLRGE (M.predict π a) (M.predict π' a) := by
  intro j j' hjj'
  set f := M.P a with hf
  have hTP := hP a
  set Aa : S → S → ℝ := fun i i' => f i j * f i' j' - f i j' * f i' j with hAa
  have hanti : ∀ i i', Aa i' i = - Aa i i' := by
    intro i i'; simp only [hAa]; ring
  set F : ℝ := ∑ i, ∑ i', π i * π' i' * Aa i i' with hF
  have e1 : M.predict π a j * M.predict π' a j' - M.predict π a j' * M.predict π' a j = F := by
    unfold POMDP.predict
    rw [Finset.sum_mul_sum, Finset.sum_mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i' _
    simp only [hAa, hf]
    ring
  have e2 : ∑ i, ∑ i', π i' * π' i * Aa i i' = -F := by
    rw [Finset.sum_comm, hF, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl; intro i _
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl; intro i' _
    rw [hanti i' i]
    ring
  have hterm : ∀ i i', 0 ≤ (π i * π' i' - π i' * π' i) * Aa i i' := by
    intro i i'
    rcases le_total i' i with hle | hle
    · apply mul_nonneg
      · have := h i i' hle; linarith
      · exact lpm_A_nonneg f hTP i i' j j' hle hjj'
    · apply mul_nonneg_of_nonpos_of_nonpos
      · have := h i' i hle; linarith
      · have := lpm_A_nonneg f hTP i' i j j' hle hjj'
        have h2 := hanti i i'
        simp only [hAa] at this h2 ⊢
        linarith
  have hsum : 0 ≤ ∑ i, ∑ i', (π i * π' i' - π i' * π' i) * Aa i i' := by
    apply Finset.sum_nonneg; intro i _
    apply Finset.sum_nonneg; intro i' _
    exact hterm i i'
  have e3 : ∑ i, ∑ i', (π i * π' i' - π i' * π' i) * Aa i i' = F - (-F) := by
    rw [← e2]
    conv_lhs => rw [show (∑ i, ∑ i', (π i * π' i' - π i' * π' i) * Aa i i') =
      ∑ i, ∑ i', (π i * π' i' * Aa i i' - π i' * π' i * Aa i i') from by
        apply Finset.sum_congr rfl; intro i _
        apply Finset.sum_congr rfl; intro i' _
        ring]
    simp only [Finset.sum_sub_distrib]
    rw [hF]
  have : 0 ≤ F := by linarith
  linarith
