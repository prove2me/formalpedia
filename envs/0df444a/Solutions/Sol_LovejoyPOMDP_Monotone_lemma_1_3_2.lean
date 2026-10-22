-- Prove2me | solution 1 for LovejoyPOMDP.Monotone.lemma_1_3_2
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T06:08:15.476163+00:00
-- url     : https://prove2.me/submissions/e148748f-d119-4e22-9ee0-bf6e9db42600

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

lemma lpm_tp_cons {S : Type*} [LinearOrder S] (f g : S → S → ℝ) (h : TPGE f g) (i i' j j' : S)
    (hii' : i ≤ i') (hjj' : j' ≤ j) :
    f i j' * g i j ≤ f i j * g i j' ∧ f i' j' * g i' j ≤ f i' j * g i' j' ∧
    f i j * g i' j' ≤ f i' j * g i j' ∧ f i' j' * g i j ≤ f i' j * g i j' ∧
    f i j' * g i' j ≤ f i' j * g i j' := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have := h i j' i j
    rwa [max_self, min_self, max_eq_right hjj', min_eq_left hjj'] at this
  · have := h i' j' i' j
    rwa [max_self, min_self, max_eq_right hjj', min_eq_left hjj'] at this
  · have := h i j i' j'
    rwa [max_eq_right hii', min_eq_left hii', max_eq_left hjj', min_eq_right hjj'] at this
  · have := h i' j' i j
    rwa [max_eq_left hii', min_eq_right hii', max_eq_right hjj', min_eq_left hjj'] at this
  · have := h i j' i' j
    rwa [max_eq_right hii', min_eq_left hii', max_eq_right hjj', min_eq_left hjj'] at this

end lpm

theorem solution {S O A : Type*} [Fintype S] [Fintype O] [Fintype A]
    [LinearOrder S] [LinearOrder O] [LinearOrder A] [Nonempty S] [Nonempty O] [Nonempty A]
    (M : POMDP S O A)
    (hP : ∀ a a' : A, a' ≤ a → TPGE (M.P a) (M.P a')) {π : S → ℝ}
    (hπ : π ∈ stdSimplex ℝ S) {a a' : A} (haa' : a' ≤ a) :
    MLRGE (M.predict π a) (M.predict π a') := by
  intro j j' hjj'
  set f := M.P a with hf
  set g := M.P a' with hg
  have hfn : ∀ x y, 0 ≤ f x y := fun x y => (M.P_row a x).1 y
  have hgn : ∀ x y, 0 ≤ g x y := fun x y => (M.P_row a' x).1 y
  have hTP := hP a a' haa'
  set B : S → S → ℝ := fun i i' => f i j * g i' j' - f i j' * g i' j with hB
  have hpair : ∀ i i', 0 ≤ B i i' + B i' i := by
    have key : ∀ i i', i ≤ i' → 0 ≤ B i i' + B i' i := by
      intro i i' hii'
      obtain ⟨c1, c2, c5, c6, c7⟩ := lpm_tp_cons f g hTP i i' j j' hii' hjj'
      have := lpm_two_pt (f i j) (f i j') (f i' j) (f i' j') (g i j) (g i j') (g i' j) (g i' j')
        (hfn _ _) (hfn _ _) (hfn _ _) (hfn _ _) (hgn _ _) (hgn _ _) (hgn _ _) (hgn _ _)
        c1 c2 c5 c6 c7
      simp only [hB]
      linarith
    intro i i'
    rcases le_total i i' with h | h
    · exact key i i' h
    · have := key i' i h; linarith
  set F : ℝ := ∑ i, ∑ i', π i * π i' * B i i' with hF
  have e1 : M.predict π a j * M.predict π a' j' - M.predict π a j' * M.predict π a' j = F := by
    unfold POMDP.predict
    rw [Finset.sum_mul_sum, Finset.sum_mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i' _
    simp only [hB, hf, hg]
    ring
  have e2 : F = ∑ i, ∑ i', π i * π i' * B i' i := by
    rw [hF, Finset.sum_comm]
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro i' _
    ring
  have hsum : 0 ≤ ∑ i, ∑ i', π i * π i' * (B i i' + B i' i) := by
    apply Finset.sum_nonneg; intro i _
    apply Finset.sum_nonneg; intro i' _
    exact mul_nonneg (mul_nonneg (hπ.1 i) (hπ.1 i')) (hpair i i')
  have e3 : ∑ i, ∑ i', π i * π i' * (B i i' + B i' i) = F + F := by
    have h1 : ∑ i, ∑ i', π i * π i' * (B i i' + B i' i) =
        ∑ i, ∑ i', π i * π i' * B i i' + ∑ i, ∑ i', π i * π i' * B i' i := by
      simp only [mul_add, Finset.sum_add_distrib]
    rw [h1, ← e2]
  have : 0 ≤ F := by linarith
  linarith
