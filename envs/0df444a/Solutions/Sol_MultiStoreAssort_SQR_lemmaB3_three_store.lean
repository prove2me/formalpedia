-- Prove2me | solution 1 for MultiStoreAssort.SQR.lemmaB3_three_store
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T16:12:05.845753+00:00
-- url     : https://prove2.me/submissions/979addf9-92dc-4bac-bb7c-b8bc1a7fa259

import Mathlib
import Definitions.Def_MultiStoreAssort_SQR_Model

open MultiStoreAssort.SQR

namespace SQR2Aux

open MultiStoreAssort.SMR

theorem discFactor_eq {m n : ℕ} (c : Fin m → Fin m → Fin n → ℝ) (cs : Fin m → ℝ)
    (hsw : StoreWiseHomog c cs) (S : Fin m → Finset (Fin n)) (i : Fin m) (k : Fin n)
    (hk : k ∈ Sbar S \ S i) : discFactor c S i k = Real.exp (-(cs i)) := by
  classical
  rw [Finset.mem_sdiff] at hk
  obtain ⟨hk1, hk2⟩ := hk
  unfold discFactor
  have hne : (Finset.univ.filter (fun j => k ∈ S j)).Nonempty := by
    unfold Sbar at hk1
    rw [Finset.mem_sup] at hk1
    obtain ⟨j, -, hj⟩ := hk1
    exact ⟨j, by simp [hj]⟩
  have hcongr : (Finset.univ.filter (fun j => k ∈ S j)).sup (fun j => (Real.exp (-(c i j k))).toNNReal)
      = (Finset.univ.filter (fun j => k ∈ S j)).sup (fun _ => (Real.exp (-(cs i))).toNNReal) := by
    apply Finset.sup_congr rfl
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    have hij : i ≠ j := by rintro rfl; exact hk2 hj
    rw [hsw.2 i j k hij]
  rw [hcongr, Finset.sup_const hne, Real.coe_toNNReal _ (Real.exp_pos _).le]

theorem storeRev_eq {m n : ℕ} (r v : Fin n → ℝ) (c : Fin m → Fin m → Fin n → ℝ) (cs : Fin m → ℝ)
    (hsw : StoreWiseHomog c cs) (S : Fin m → Finset (Fin n)) (i : Fin m) :
    ∑ k, r k * pQ v c S i k = rev8 r v (Real.exp (-(cs i))) (Sbar S) (S i) := by
  classical
  have hSi : S i ⊆ Sbar S := by
    intro x hx; unfold Sbar; exact Finset.mem_sup.mpr ⟨i, Finset.mem_univ _, hx⟩
  set β := Real.exp (-(cs i))
  set A := Sbar S \ S i
  have hdisj : Disjoint (S i) A := Finset.disjoint_sdiff
  have hden : denomM v c S i = 1 + Vs v (S i) + β * Vs v A := by
    unfold denomM Vs
    rw [Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro l hl; rw [discFactor_eq c cs hsw S i l hl]; ring
  rw [← Finset.sum_subset (Finset.subset_univ (S i ∪ A))]
  · rw [Finset.sum_union hdisj]
    have h1 : ∑ k ∈ S i, r k * pQ v c S i k = Ws r v (S i) / (1 + Vs v (S i)) := by
      unfold Ws Vs; rw [Finset.sum_div]
      apply Finset.sum_congr rfl; intro k hk
      simp only [pQ, hk, if_true]; ring
    have h2 : ∑ k ∈ A, r k * pQ v c S i k =
        β * Ws r v A / ((1 + Vs v (S i)) * (1 + Vs v (S i) + β * Vs v A)) := by
      unfold Ws; rw [Finset.mul_sum, Finset.sum_div]
      apply Finset.sum_congr rfl; intro k hk
      have hk' : k ∉ S i := (Finset.mem_sdiff.mp hk).2
      have hk2 : k ∈ Sbar S \ S i := hk
      rw [pQ, if_neg hk', if_pos hk2, discFactor_eq c cs hsw S i k hk, ← hden]
      unfold Vs; ring
    rw [h1, h2]; rfl
  · intro k _ hk
    have h1 : k ∉ S i := fun h => hk (Finset.mem_union_left _ h)
    have h2 : k ∉ A := fun h => hk (Finset.mem_union_right _ h)
    simp [pQ, h1, h2, A]

theorem revQ_eq {m n : ℕ} (lam : Fin m → ℝ) (r v : Fin n → ℝ) (c : Fin m → Fin m → Fin n → ℝ)
    (cs : Fin m → ℝ) (hsw : StoreWiseHomog c cs) (S : Fin m → Finset (Fin n)) :
    revQ lam r v c S = ∑ i, lam i * rev8 r v (Real.exp (-(cs i))) (Sbar S) (S i) := by
  unfold revQ
  apply Finset.sum_congr rfl; intro i _
  rw [storeRev_eq r v c cs hsw S i]

theorem Sbar_eq {m n : ℕ} (S : Fin m → Finset (Fin n)) (L : Fin m) (h : ∀ i, S i ⊆ S L) :
    Sbar S = S L := by
  unfold Sbar
  apply le_antisymm
  · exact Finset.sup_le (fun i _ => h i)
  · exact Finset.le_sup (f := S) (Finset.mem_univ L)

end SQR2Aux

namespace SQR2B3

set_option maxHeartbeats 4000000 in
theorem polyx_C2A (a b c d x : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    0 ≤ (((1 + a) * (1 + a + b) / ((1 + a + c) * (1 + a + b + c))) * (x / ((1 + a) * (1 + a + x * (b + c + d))) - 1 / (1 + a + b)) + 1 / (1 + a + b + c) - x / ((1 + a + c) * (1 + a + c + x * (b + d)))) := by
  have hD : 0 < (a + c + 1)*(a + b + c + 1)*(a + b*x + c + d*x + 1)*(a + b*x + c*x + d*x + 1) := by positivity
  have key : (((1 + a) * (1 + a + b) / ((1 + a + c) * (1 + a + b + c))) * (x / ((1 + a) * (1 + a + x * (b + c + d))) - 1 / (1 + a + b)) + 1 / (1 + a + b + c) - x / ((1 + a + c) * (1 + a + c + x * (b + d)))) = (a^2*c + 2*a*b*c*x + a*c^2*x + a*c^2 + 2*a*c*d*x - a*c*x^2 + 2*a*c + b^2*c*x^2 + b*c^2*x^2 + b*c^2*x + 2*b*c*d*x^2 - 2*b*c*x^2 + 3*b*c*x + c^3*x + c^2*d*x^2 + c^2*d*x - c^2*x^2 + c^2*x + c^2 + c*d^2*x^2 - c*d*x^2 + 2*c*d*x - c*x^2 + c) / ((a + c + 1)*(a + b + c + 1)*(a + b*x + c + d*x + 1)*(a + b*x + c*x + d*x + 1)) := by
    rw [eq_div_iff hD.ne']
    field_simp
    ring
  rw [key]
  apply div_nonneg _ hD.le
  have key2 : ∀ u : ℝ, u = 1 - x → a^2*c + 2*a*b*c*x + a*c^2*x + a*c^2 + 2*a*c*d*x - a*c*x^2 + 2*a*c + b^2*c*x^2 + b*c^2*x^2 + b*c^2*x + 2*b*c*d*x^2 - 2*b*c*x^2 + 3*b*c*x + c^3*x + c^2*d*x^2 + c^2*d*x - c^2*x^2 + c^2*x + c^2 + c*d^2*x^2 - c*d*x^2 + 2*c*d*x - c*x^2 + c = a^2*c*u^2 + 2*a^2*c*u*x + a^2*c*x^2 + 2*a*b*c*u*x + 2*a*b*c*x^2 + a*c^2*u^2 + 3*a*c^2*u*x + 2*a*c^2*x^2 + 2*a*c*d*u*x + 2*a*c*d*x^2 + 2*a*c*u^2 + 4*a*c*u*x + a*c*x^2 + b^2*c*x^2 + b*c^2*u*x + 2*b*c^2*x^2 + 2*b*c*d*x^2 + 3*b*c*u*x + b*c*x^2 + c^3*u*x + c^3*x^2 + c^2*d*u*x + 2*c^2*d*x^2 + c^2*u^2 + 3*c^2*u*x + c^2*x^2 + c*d^2*x^2 + 2*c*d*u*x + c*d*x^2 + c*u^2 + 2*c*u*x := by
    intro u hu
    subst hu
    ring
  rw [key2 (1 - x) rfl]
  have hu : 0 ≤ 1 - x := by linarith
  set u := 1 - x
  positivity


set_option maxHeartbeats 4000000 in
theorem polyx_C23A (a b c d x : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    0 ≤ ((((1 + a) * (1 + a + b) / ((1 + a + c) * (1 + a + b + c))) * (x / ((1 + a) * (1 + a + x * (b + c + d))) - 1 / (1 + a + b)) + 1 / (1 + a + b + c) - x / ((1 + a + c) * (1 + a + c + x * (b + d)))) * b + (((1 + a) * (1 + a + b) / ((1 + a + c) * (1 + a + b + c))) * (x / ((1 + a) * (1 + a + x * (b + c + d))) - x / ((1 + a + b) * (1 + a + b + x * (c + d)))) + 1 / (1 + a + b + c) - 1 / (1 + a + c)) * c) := by
  have hD : 0 < (a + c + 1)*(a + b + c + 1)*(a + b + c*x + d*x + 1)*(a + b*x + c + d*x + 1)*(a + b*x + c*x + d*x + 1) := by positivity
  have key : ((((1 + a) * (1 + a + b) / ((1 + a + c) * (1 + a + b + c))) * (x / ((1 + a) * (1 + a + x * (b + c + d))) - 1 / (1 + a + b)) + 1 / (1 + a + b + c) - x / ((1 + a + c) * (1 + a + c + x * (b + d)))) * b + (((1 + a) * (1 + a + b) / ((1 + a + c) * (1 + a + b + c))) * (x / ((1 + a) * (1 + a + x * (b + c + d))) - x / ((1 + a + b) * (1 + a + b + x * (c + d)))) + 1 / (1 + a + b + c) - 1 / (1 + a + c)) * c) = (-2*a^2*b*c*x^2 + 2*a^2*b*c*x - a*b^2*c*x^3 - a*b^2*c*x^2 + 2*a*b^2*c*x - a*b*c^2*x^3 - a*b*c^2*x^2 + 2*a*b*c^2*x - 2*a*b*c*d*x^3 + 2*a*b*c*d*x^2 - 4*a*b*c*x^2 + 4*a*b*c*x - b^3*c*x^2 + b^3*c*x - b^2*c^2*x^3 + b^2*c^2*x - b^2*c*d*x^3 + b^2*c*d*x^2 - b^2*c*x^3 - b^2*c*x^2 + 2*b^2*c*x - b*c^3*x^3 + b*c^3*x^2 - b*c^2*d*x^3 + b*c^2*d*x^2 - b*c^2*x^3 - b*c^2*x^2 + 2*b*c^2*x - 2*b*c*d*x^3 + 2*b*c*d*x^2 - 2*b*c*x^2 + 2*b*c*x) / ((a + c + 1)*(a + b + c + 1)*(a + b + c*x + d*x + 1)*(a + b*x + c + d*x + 1)*(a + b*x + c*x + d*x + 1)) := by
    rw [eq_div_iff hD.ne']
    field_simp
    ring
  rw [key]
  apply div_nonneg _ hD.le
  have key2 : ∀ u : ℝ, u = 1 - x → -2*a^2*b*c*x^2 + 2*a^2*b*c*x - a*b^2*c*x^3 - a*b^2*c*x^2 + 2*a*b^2*c*x - a*b*c^2*x^3 - a*b*c^2*x^2 + 2*a*b*c^2*x - 2*a*b*c*d*x^3 + 2*a*b*c*d*x^2 - 4*a*b*c*x^2 + 4*a*b*c*x - b^3*c*x^2 + b^3*c*x - b^2*c^2*x^3 + b^2*c^2*x - b^2*c*d*x^3 + b^2*c*d*x^2 - b^2*c*x^3 - b^2*c*x^2 + 2*b^2*c*x - b*c^3*x^3 + b*c^3*x^2 - b*c^2*d*x^3 + b*c^2*d*x^2 - b*c^2*x^3 - b*c^2*x^2 + 2*b*c^2*x - 2*b*c*d*x^3 + 2*b*c*d*x^2 - 2*b*c*x^2 + 2*b*c*x = 2*a^2*b*c*u^2*x + 2*a^2*b*c*u*x^2 + 2*a*b^2*c*u^2*x + 3*a*b^2*c*u*x^2 + 2*a*b*c^2*u^2*x + 3*a*b*c^2*u*x^2 + 2*a*b*c*d*u*x^2 + 4*a*b*c*u^2*x + 4*a*b*c*u*x^2 + b^3*c*u^2*x + b^3*c*u*x^2 + b^2*c^2*u^2*x + 2*b^2*c^2*u*x^2 + b^2*c*d*u*x^2 + 2*b^2*c*u^2*x + 3*b^2*c*u*x^2 + b*c^3*u*x^2 + b*c^2*d*u*x^2 + 2*b*c^2*u^2*x + 3*b*c^2*u*x^2 + 2*b*c*d*u*x^2 + 2*b*c*u^2*x + 2*b*c*u*x^2 := by
    intro u hu
    subst hu
    ring
  rw [key2 (1 - x) rfl]
  have hu : 0 ≤ 1 - x := by linarith
  set u := 1 - x
  positivity



set_option maxHeartbeats 4000000 in
theorem c4_struct (a b c d x : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hx : 0 ≤ x) (hx1 : x ≤ 1) : 0 ≤ (((1 + a) * (1 + a + b) / ((1 + a + c) * (1 + a + b + c))) * (x / ((1 + a) * (1 + a + x * (b + c + d))) - x / ((1 + a + b) * (1 + a + b + x * (c + d)))) + x / ((1 + a + b + c) * (1 + a + b + c + x * d)) - x / ((1 + a + c) * (1 + a + c + x * (b + d)))) := by
  have p1 : 0 < 1 + a := by linarith
  have p12 : 0 < 1 + a + b := by linarith
  have p13 : 0 < 1 + a + c := by linarith
  have p123 : 0 < 1 + a + b + c := by linarith
  have b1 : 0 < 1 + a + b + c + x * d := by positivity
  have b2 : 0 < 1 + a + x * (b + c + d) := by positivity
  have b3 : 0 < 1 + a + c + x * (b + d) := by positivity
  have b4 : 0 < 1 + a + b + x * (c + d) := by positivity
  have key : (((1 + a) * (1 + a + b) / ((1 + a + c) * (1 + a + b + c))) * (x / ((1 + a) * (1 + a + x * (b + c + d))) - x / ((1 + a + b) * (1 + a + b + x * (c + d)))) + x / ((1 + a + b + c) * (1 + a + b + c + x * d)) - x / ((1 + a + c) * (1 + a + c + x * (b + d)))) = x / ((1 + a + c) * (1 + a + b + c)) *
      (((1 + a + c) * (1 + a + x * (b + c + d)) + (1 + a + b) * (1 + a + b + c + x * d)) *
        ((1 + a + c + x * (b + d)) * (1 + a + b + x * (c + d)) -
          (1 + a + b + c + x * d) * (1 + a + x * (b + c + d))) /
        ((1 + a + b + c + x * d) * (1 + a + x * (b + c + d)) *
          ((1 + a + c + x * (b + d)) * (1 + a + b + x * (c + d))))) := by
    field_simp
    ring
  rw [key]
  have hprod : (1 + a + c + x * (b + d)) * (1 + a + b + x * (c + d)) -
      (1 + a + b + c + x * d) * (1 + a + x * (b + c + d)) = b * c * (1 - x) * (1 - x) := by ring
  rw [hprod]
  have hu : 0 ≤ 1 - x := by linarith
  positivity
noncomputable def h (β G P w y : ℝ) : ℝ := G / P + β * w / (P * (P + β * y))

theorem frac_diff (K V s t : ℝ) (hK : 0 < K) (hs : 0 < K + s * V) (ht : 0 < K + t * V) :
    t / (K * (K + t * V)) - s / (K * (K + s * V)) = (t - s) / ((K + t * V) * (K + s * V)) := by
  rw [div_sub_div _ _ (mul_ne_zero hK.ne' ht.ne') (mul_ne_zero hK.ne' hs.ne'),
    div_eq_div_iff (mul_ne_zero (mul_ne_zero hK.ne' ht.ne') (mul_ne_zero hK.ne' hs.ne'))
      (mul_ne_zero ht.ne' hs.ne')]
  ring

set_option maxHeartbeats 4000000 in
/-- The four-group inequality behind Lemma B.3 and its mirror (Case 2 of Proposition B.1). -/
theorem b3_coreA (a b c d W1 W2 W3 W4 x y : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hW2 : 0 ≤ W2) (hW3 : 0 ≤ W3) (hW4 : 0 ≤ W4) (hb0 : b = 0 → W2 = 0) (hc0 : c = 0 → W3 = 0)
    (hy : 0 ≤ y) (hxy : y ≤ x) (hx1 : x ≤ 1) :
    (b * W3 ≤ c * W2 → 0 ≤ ((1 + a) * (1 + a + b) / ((1 + a + c) * (1 + a + b + c))) * ((h x W1 (1 + a) (W2 + W3 + W4) (b + c + d)) - (h x (W1 + W2) (1 + (a + b)) (W3 + W4) (c + d))) + ((h y (W1 + W2 + W3) (1 + (a + b + c)) W4 d) - (h y (W1 + W3) (1 + (a + c)) (W2 + W4) (b + d)))) := by
  have hx : 0 ≤ x := le_trans hy hxy
  -- monotonicity in the second discount factor
  have hm1 : y / ((1 + a + c) * (1 + a + c + y * (b + d))) ≤ x / ((1 + a + c) * (1 + a + c + x * (b + d))) := by
    have e := frac_diff (1 + a + c) (b + d) y x (by linarith) (by nlinarith) (by nlinarith)
    have : 0 ≤ (x - y) / ((1 + a + c + x * (b + d)) * (1 + a + c + y * (b + d))) := by
      apply div_nonneg (by linarith)
      have : 0 < 1 + a + c + x * (b + d) := by nlinarith
      have : 0 < 1 + a + c + y * (b + d) := by nlinarith
      positivity
    linarith
  have hm2 : x / ((1 + a + b + c) * (1 + a + b + c + x * d)) - x / ((1 + a + c) * (1 + a + c + x * (b + d))) ≤
      y / ((1 + a + b + c) * (1 + a + b + c + y * d)) - y / ((1 + a + c) * (1 + a + c + y * (b + d))) := by
    have e1 := frac_diff (1 + a + b + c) d y x (by linarith) (by nlinarith) (by nlinarith)
    have e2 := frac_diff (1 + a + c) (b + d) y x (by linarith) (by nlinarith) (by nlinarith)
    have p1 : 0 < 1 + a + c + x * (b + d) := by nlinarith
    have p2 : 0 < 1 + a + c + y * (b + d) := by nlinarith
    have q1 : 1 + a + c + x * (b + d) ≤ 1 + a + b + c + x * d := by nlinarith
    have q2 : 1 + a + c + y * (b + d) ≤ 1 + a + b + c + y * d := by nlinarith
    have : (x - y) / ((1 + a + b + c + x * d) * (1 + a + b + c + y * d)) ≤
        (x - y) / ((1 + a + c + x * (b + d)) * (1 + a + c + y * (b + d))) := by
      apply div_le_div_of_nonneg_left (by linarith) (mul_pos p1 p2)
      exact mul_le_mul q1 q2 p2.le (by linarith)
    linarith
  have A2 := polyx_C2A a b c d x ha hb hc hd hx hx1
  have A23 := polyx_C23A a b c d x ha hb hc hd hx hx1
  have A4 := c4_struct a b c d x ha hb hc hd hx hx1
  have hC1A : ((1 + a) * (1 + a + b) / ((1 + a + c) * (1 + a + b + c)) * (1 / (1 + a) - 1 / (1 + a + b)) + 1 / (1 + a + b + c) - 1 / (1 + a + c)) = 0 := by field_simp; ring
  intro hcase
  · 
    have e : ((1 + a) * (1 + a + b) / ((1 + a + c) * (1 + a + b + c))) * ((h x W1 (1 + a) (W2 + W3 + W4) (b + c + d)) - (h x (W1 + W2) (1 + (a + b)) (W3 + W4) (c + d))) + ((h y (W1 + W2 + W3) (1 + (a + b + c)) W4 d) - (h y (W1 + W3) (1 + (a + c)) (W2 + W4) (b + d))) =
        ((1 + a) * (1 + a + b) / ((1 + a + c) * (1 + a + b + c)) * (1 / (1 + a) - 1 / (1 + a + b)) + 1 / (1 + a + b + c) - 1 / (1 + a + c)) * W1 + (((1 + a) * (1 + a + b) / ((1 + a + c) * (1 + a + b + c))) * (x / ((1 + a) * (1 + a + x * (b + c + d))) - 1 / (1 + a + b)) + 1 / (1 + a + b + c) - y / ((1 + a + c) * (1 + a + c + y * (b + d)))) * W2 + (((1 + a) * (1 + a + b) / ((1 + a + c) * (1 + a + b + c))) * (x / ((1 + a) * (1 + a + x * (b + c + d))) - x / ((1 + a + b) * (1 + a + b + x * (c + d)))) + 1 / (1 + a + b + c) - 1 / (1 + a + c)) * W3 + (((1 + a) * (1 + a + b) / ((1 + a + c) * (1 + a + b + c))) * (x / ((1 + a) * (1 + a + x * (b + c + d))) - x / ((1 + a + b) * (1 + a + b + x * (c + d)))) + y / ((1 + a + b + c) * (1 + a + b + c + y * d)) - y / ((1 + a + c) * (1 + a + c + y * (b + d)))) * W4 := by
      unfold h; ring
    rw [e, hC1A, zero_mul, zero_add]
    have c2 : 0 ≤ (((1 + a) * (1 + a + b) / ((1 + a + c) * (1 + a + b + c))) * (x / ((1 + a) * (1 + a + x * (b + c + d))) - 1 / (1 + a + b)) + 1 / (1 + a + b + c) - y / ((1 + a + c) * (1 + a + c + y * (b + d)))) := by linarith
    have c23 : 0 ≤ (((1 + a) * (1 + a + b) / ((1 + a + c) * (1 + a + b + c))) * (x / ((1 + a) * (1 + a + x * (b + c + d))) - 1 / (1 + a + b)) + 1 / (1 + a + b + c) - y / ((1 + a + c) * (1 + a + c + y * (b + d)))) * b + (((1 + a) * (1 + a + b) / ((1 + a + c) * (1 + a + b + c))) * (x / ((1 + a) * (1 + a + x * (b + c + d))) - x / ((1 + a + b) * (1 + a + b + x * (c + d)))) + 1 / (1 + a + b + c) - 1 / (1 + a + c)) * c := by nlinarith
    have c4 : 0 ≤ (((1 + a) * (1 + a + b) / ((1 + a + c) * (1 + a + b + c))) * (x / ((1 + a) * (1 + a + x * (b + c + d))) - x / ((1 + a + b) * (1 + a + b + x * (c + d)))) + y / ((1 + a + b + c) * (1 + a + b + c + y * d)) - y / ((1 + a + c) * (1 + a + c + y * (b + d)))) := by linarith
    have c4w : 0 ≤ (((1 + a) * (1 + a + b) / ((1 + a + c) * (1 + a + b + c))) * (x / ((1 + a) * (1 + a + x * (b + c + d))) - x / ((1 + a + b) * (1 + a + b + x * (c + d)))) + y / ((1 + a + b + c) * (1 + a + b + c + y * d)) - y / ((1 + a + c) * (1 + a + c + y * (b + d)))) * W4 := mul_nonneg c4 hW4
    set C2 := (((1 + a) * (1 + a + b) / ((1 + a + c) * (1 + a + b + c))) * (x / ((1 + a) * (1 + a + x * (b + c + d))) - 1 / (1 + a + b)) + 1 / (1 + a + b + c) - y / ((1 + a + c) * (1 + a + c + y * (b + d))))
    set C3 := (((1 + a) * (1 + a + b) / ((1 + a + c) * (1 + a + b + c))) * (x / ((1 + a) * (1 + a + x * (b + c + d))) - x / ((1 + a + b) * (1 + a + b + x * (c + d)))) + 1 / (1 + a + b + c) - 1 / (1 + a + c))
    have key : 0 ≤ C2 * W2 + C3 * W3 := by
      rcases hc.lt_or_eq with hcp | hc0'
      · have e2 : c * (C2 * W2 + C3 * W3) = C2 * (c * W2 - b * W3) + W3 * (C2 * b + C3 * c) := by ring
        have : 0 ≤ c * (C2 * W2 + C3 * W3) := by
          rw [e2]; exact add_nonneg (mul_nonneg c2 (by linarith)) (mul_nonneg hW3 c23)
        by_contra hneg; push Not at hneg
        have := mul_neg_of_pos_of_neg hcp hneg; linarith
      · rw [hc0 hc0'.symm]; simp only [mul_zero, add_zero]; exact mul_nonneg c2 hW2
    linarith
end SQR2B3

open MultiStoreAssort.SQR MultiStoreAssort.SMR in
theorem solution (R V : Fin 4 → ℝ) (c : Fin 3 → Fin 3 → Fin 4 → ℝ) (c₁ c₂ c₃ : ℝ)
    (hR : ∀ k, 0 ≤ R k) (hV : ∀ k, 0 ≤ V k) (hcii : ∀ i k, c i i k = 0)
    (hsw : StoreWiseHomog c ![c₁, c₂, c₃]) (hR23 : R 2 ≤ R 1) (hc12 : c₁ ≤ c₂) :
    MultiStoreAssort.SMR.revQ ![1 / 2, 1 / 2, 0] R V c (![{0, 1}, {0, 2}, {3}] : Fin 3 → Finset (Fin 4)) ≤
      max (MultiStoreAssort.SMR.revQ ![1 / 2, 1 / 2, 0] R V c (![{0}, {0, 1, 2}, {3}] : Fin 3 → Finset (Fin 4)))
        (MultiStoreAssort.SMR.revQ ![1 / 2, 1 / 2, 0] R V c (![{0, 1}, {0, 1, 2}, {3}] : Fin 3 → Finset (Fin 4))) := by
  classical
  set x := Real.exp (-c₁)
  set y := Real.exp (-c₂)
  have hy0 : 0 ≤ y := (Real.exp_pos _).le
  have hxy : y ≤ x := Real.exp_le_exp.mpr (by linarith)
  have hx1 : x ≤ 1 := Real.exp_le_one_iff.mpr (by have := hsw.1 0; simp at this; linarith)
  have hU : ∀ S : Fin 3 → Finset (Fin 4), S = ![{0, 1}, {0, 2}, {3}] ∨ S = ![{0}, {0, 1, 2}, {3}] ∨
      S = ![{0, 1}, {0, 1, 2}, {3}] → Sbar S = Finset.univ := by
    rintro S (rfl | rfl | rfl) <;> decide
  have hrev : ∀ S : Fin 3 → Finset (Fin 4), Sbar S = Finset.univ →
      revQ ![1 / 2, 1 / 2, 0] R V c S =
        1 / 2 * rev8 R V x Finset.univ (S 0) + 1 / 2 * rev8 R V y Finset.univ (S 1) := by
    intro S hS
    rw [SQR2Aux.revQ_eq _ R V c ![c₁, c₂, c₃] hsw S, hS, Fin.sum_univ_three]
    simp [x, y]
  rw [hrev _ (hU _ (Or.inl rfl)), hrev _ (hU _ (Or.inr (Or.inl rfl))), hrev _ (hU _ (Or.inr (Or.inr rfl)))]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  have core := SQR2B3.b3_coreA (V 0) (V 1) (V 2) (V 3) (R 0 * V 0) (R 1 * V 1) (R 2 * V 2) (R 3 * V 3) x y
    (hV 0) (hV 1) (hV 2) (hV 3) (mul_nonneg (hR 1) (hV 1)) (mul_nonneg (hR 2) (hV 2))
    (mul_nonneg (hR 3) (hV 3)) (fun h => by rw [h, mul_zero]) (fun h => by rw [h, mul_zero])
    hy0 hxy hx1 (by nlinarith [mul_nonneg (hV 1) (hV 2), mul_le_mul_of_nonneg_left hR23 (mul_nonneg (hV 1) (hV 2))])
  -- evaluate the five store revenues
  have e01 : rev8 R V x Finset.univ {0, 1} = SQR2B3.h x (R 0 * V 0 + R 1 * V 1) (1 + (V 0 + V 1))
      (R 2 * V 2 + R 3 * V 3) (V 2 + V 3) := by
    have : (Finset.univ : Finset (Fin 4)) \ {0, 1} = {2, 3} := by decide
    unfold rev8 SQR2B3.h; rw [this]; simp [Ws, Vs, Finset.sum_pair]
  have e02 : rev8 R V y Finset.univ {0, 2} = SQR2B3.h y (R 0 * V 0 + R 2 * V 2) (1 + (V 0 + V 2))
      (R 1 * V 1 + R 3 * V 3) (V 1 + V 3) := by
    have : (Finset.univ : Finset (Fin 4)) \ {0, 2} = {1, 3} := by decide
    unfold rev8 SQR2B3.h; rw [this]; simp [Ws, Vs, Finset.sum_pair]
  have e0 : rev8 R V x Finset.univ {0} = SQR2B3.h x (R 0 * V 0) (1 + V 0)
      (R 1 * V 1 + R 2 * V 2 + R 3 * V 3) (V 1 + V 2 + V 3) := by
    have : (Finset.univ : Finset (Fin 4)) \ {0} = {1, 2, 3} := by decide
    unfold rev8 SQR2B3.h; rw [this]
    simp [Ws, Vs, Finset.sum_insert, Finset.sum_pair]; ring
  have e012 : rev8 R V y Finset.univ {0, 1, 2} = SQR2B3.h y (R 0 * V 0 + R 1 * V 1 + R 2 * V 2)
      (1 + (V 0 + V 1 + V 2)) (R 3 * V 3) (V 3) := by
    have : (Finset.univ : Finset (Fin 4)) \ {0, 1, 2} = {3} := by decide
    unfold rev8 SQR2B3.h; rw [this]
    simp [Ws, Vs, Finset.sum_insert, Finset.sum_pair]; ring
  rw [e01, e02, e0, e012]
  set γ := (1 + V 0) * (1 + V 0 + V 1) / ((1 + V 0 + V 2) * (1 + V 0 + V 1 + V 2))
  have hγ0 : 0 ≤ γ := by have := hV 0; have := hV 1; have := hV 2; positivity
  have hγ1 : γ ≤ 1 := by
    have := hV 0; have := hV 1; have := hV 2
    rw [div_le_one (by positivity)]
    exact mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith)
  set A := SQR2B3.h x (R 0 * V 0) (1 + V 0) (R 1 * V 1 + R 2 * V 2 + R 3 * V 3) (V 1 + V 2 + V 3)
  set B := SQR2B3.h x (R 0 * V 0 + R 1 * V 1) (1 + (V 0 + V 1)) (R 2 * V 2 + R 3 * V 3) (V 2 + V 3)
  set Cm := SQR2B3.h y (R 0 * V 0 + R 1 * V 1 + R 2 * V 2) (1 + (V 0 + V 1 + V 2)) (R 3 * V 3) (V 3)
  set D := SQR2B3.h y (R 0 * V 0 + R 2 * V 2) (1 + (V 0 + V 2)) (R 1 * V 1 + R 3 * V 3) (V 1 + V 3)
  have hc : 0 ≤ γ * (A - B) + (Cm - D) := by simpa [A, B, Cm, D, γ, add_assoc] using core
  rcases le_total A B with hAB | hAB
  · apply le_max_of_le_right; nlinarith
  · apply le_max_of_le_left; nlinarith
