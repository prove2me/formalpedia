-- Prove2me | solution 1 for LovejoyPOMDP.Monotone.lemma_1_2_2
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T06:08:16.518979+00:00
-- url     : https://prove2.me/submissions/bc7dc426-ef97-4920-8d1f-671166d5408c

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

lemma lpm_predict_sum (M : POMDP S O A) {π : S → ℝ} (hπ : π ∈ stdSimplex ℝ S) (a : A) :
    ∑ j, M.predict π a j = 1 := by
  unfold POMDP.predict
  rw [Finset.sum_comm]
  have : ∀ i, ∑ j, π i * M.P a i j = π i := by
    intro i
    rw [← Finset.mul_sum, (M.P_row a i).2, mul_one]
  rw [Finset.sum_congr rfl (fun i _ => this i)]
  exact hπ.2

lemma lpm_sigma_eq (M : POMDP S O A) (π : S → ℝ) (a : A) (k : O) :
    M.sigma π a k = ∑ j, M.predict π a j * M.R a j k := by
  unfold POMDP.sigma POMDP.predict
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_mul]

lemma lpm_sigma_pos (M : POMDP S O A) {π : S → ℝ} (hπ : π ∈ stdSimplex ℝ S) (a : A) (k : O) :
    0 < M.sigma π a k := by
  rw [lpm_sigma_eq]
  apply Finset.sum_pos'
  · intro j _
    exact mul_nonneg (lpm_predict_nonneg M hπ a j) (M.R_pos a j k).le
  · by_contra hcon
    push_neg at hcon
    have h1 : ∀ j, M.predict π a j = 0 := by
      intro j
      have h2 := hcon j (Finset.mem_univ j)
      have h3 := mul_nonneg (lpm_predict_nonneg M hπ a j) (M.R_pos a j k).le
      have h4 : M.predict π a j * M.R a j k = 0 := le_antisymm h2 h3
      rcases mul_eq_zero.1 h4 with h | h
      · exact h
      · exact absurd h (M.R_pos a j k).ne'
    have := lpm_predict_sum M hπ a
    simp [h1] at this

end lpm

theorem solution {S O A : Type*} [Fintype S] [Fintype O] [Fintype A]
    [LinearOrder S] [LinearOrder O] [LinearOrder A] [Nonempty S] [Nonempty O] [Nonempty A]
    (M : POMDP S O A) (a : A) (k : O) :
    (∀ π π' : S → ℝ, π ∈ stdSimplex ℝ S → π' ∈ stdSimplex ℝ S → MLRGE π π' →
        MLRGE (M.bayes π a k) (M.bayes π' a k)) ↔
      (∀ π π' : S → ℝ, π ∈ stdSimplex ℝ S → π' ∈ stdSimplex ℝ S → MLRGE π π' →
        MLRGE (M.predict π a) (M.predict π' a)) := by
  constructor
  · intro h π π' hπ hπ' hmlr j j' hjj'
    have hb := h π π' hπ hπ' hmlr j j' hjj'
    rw [lpm_bayes_eq, lpm_bayes_eq, lpm_bayes_eq, lpm_bayes_eq, div_mul_div_comm,
      div_mul_div_comm] at hb
    have hσ := lpm_sigma_pos M hπ a k
    have hσ' := lpm_sigma_pos M hπ' a k
    have hr1 := M.R_pos a j' k
    have hr2 := M.R_pos a j k
    rw [div_le_div_iff_of_pos_right (mul_pos hσ hσ')] at hb
    have e1 : M.predict π a j' * M.R a j' k * (M.predict π' a j * M.R a j k) =
        (M.predict π a j' * M.predict π' a j) * (M.R a j' k * M.R a j k) := by ring
    have e2 : M.predict π a j * M.R a j k * (M.predict π' a j' * M.R a j' k) =
        (M.predict π a j * M.predict π' a j') * (M.R a j' k * M.R a j k) := by ring
    rw [e1, e2] at hb
    exact le_of_mul_le_mul_right hb (mul_pos hr1 hr2)
  · intro h π π' hπ hπ' hmlr j j' hjj'
    have hp := h π π' hπ hπ' hmlr j j' hjj'
    rw [lpm_bayes_eq, lpm_bayes_eq, lpm_bayes_eq, lpm_bayes_eq, div_mul_div_comm,
      div_mul_div_comm]
    apply div_le_div_of_nonneg_right _ (mul_nonneg (lpm_sigma_nonneg M hπ a k) (lpm_sigma_nonneg M hπ' a k))
    have hr1 := (M.R_pos a j' k).le
    have hr2 := (M.R_pos a j k).le
    calc M.predict π a j' * M.R a j' k * (M.predict π' a j * M.R a j k)
        = (M.predict π a j' * M.predict π' a j) * (M.R a j' k * M.R a j k) := by ring
      _ ≤ (M.predict π a j * M.predict π' a j') * (M.R a j' k * M.R a j k) :=
          mul_le_mul_of_nonneg_right hp (mul_nonneg hr1 hr2)
      _ = M.predict π a j * M.R a j k * (M.predict π' a j' * M.R a j' k) := by ring
