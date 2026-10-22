-- Prove2me | solution 1 for LovejoyPOMDP.Monotone.lemma_1_2_1
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T06:05:07.645252+00:00
-- url     : https://prove2.me/submissions/4a9f0455-10b4-4ca8-803f-21fa341d8b57

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

end lpm

theorem solution {S O A : Type*} [Fintype S] [Fintype O] [Fintype A]
    [LinearOrder S] [LinearOrder O] [LinearOrder A] [Nonempty S] [Nonempty O] [Nonempty A]
    (M : POMDP S O A) (a : A)
    (hR : ∀ j j' : S, j' ≤ j → MLRGE (M.R a j) (M.R a j'))
    {π : S → ℝ} (hπ : π ∈ stdSimplex ℝ S) {k k' : O} (hkk' : k' ≤ k) :
    MLRGE (M.bayes π a k) (M.bayes π a k') := by
  intro j j' hjj'
  rw [lpm_bayes_eq, lpm_bayes_eq, lpm_bayes_eq, lpm_bayes_eq]
  rw [div_mul_div_comm, div_mul_div_comm]
  apply div_le_div_of_nonneg_right _ (mul_nonneg (lpm_sigma_nonneg M hπ a k) (lpm_sigma_nonneg M hπ a k'))
  have h1 := hR j j' hjj' k k' hkk'
  have hw1 := lpm_predict_nonneg M hπ a j'
  have hw3 := lpm_predict_nonneg M hπ a j
  calc M.predict π a j' * M.R a j' k * (M.predict π a j * M.R a j k')
      = (M.predict π a j' * M.predict π a j) * (M.R a j k' * M.R a j' k) := by ring
    _ ≤ (M.predict π a j' * M.predict π a j) * (M.R a j k * M.R a j' k') := by
        apply mul_le_mul_of_nonneg_left h1 (mul_nonneg hw1 hw3)
    _ = M.predict π a j * M.R a j k * (M.predict π a j' * M.R a j' k') := by ring
