-- Prove2me | solution 1 for NamikiStretch.Lossy.eq_18
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-01T19:57:17.222209+00:00
-- url     : https://prove2.me/submissions/c0c23d5b-b215-4cf1-b4e4-c2f388d08dcc

import Mathlib
import Definitions.Def_NamikiStretch_Lossy_Protocol

open MeasureTheory Finset Filter
open scoped Topology
open QAlgorithms.Papers.Independent.Dependency50.P39
open QAlgorithms.Papers.Independent.Frontier30.P21
open NamikiStretch.Lossy

noncomputable section

lemma sum_range_ite_ge {α : Type*} [AddCommMonoid α] (a b : ℕ) (hab : a ≤ b) (f : ℕ → α) :
    (∑ k ∈ range (b + 1), if a ≤ k then f (k - a) else 0) =
      ∑ s ∈ range (b - a + 1), f s := by
  have hb : b + 1 = a + (b - a + 1) := by omega
  rw [hb, sum_range_add]
  have h1 : (∑ x ∈ range a, if a ≤ x then f (x - a) else 0) = 0 := by
    apply sum_eq_zero
    intro x hx
    rw [mem_range] at hx
    rw [if_neg (by omega)]
  rw [h1, zero_add]
  apply sum_congr rfl
  intro s _
  rw [if_pos (by omega), Nat.add_sub_cancel_left]

lemma sum_range_ite_interval {α : Type*} [AddCommMonoid α] (N a b : ℕ) (hab : a ≤ b) (hbN : b ≤ N)
    (f : ℕ → α) :
    (∑ k ∈ range (N + 1), if a ≤ k ∧ k ≤ b then f (k - a) else 0) =
      ∑ s ∈ range (b - a + 1), f s := by
  have hN : N + 1 = (b + 1) + (N - b) := by omega
  rw [hN, sum_range_add]
  have h2 : (∑ x ∈ range (N - b), if a ≤ b + 1 + x ∧ b + 1 + x ≤ b then f (b + 1 + x - a) else 0) = 0 := by
    apply sum_eq_zero
    intro x _
    rw [if_neg (by omega)]
  rw [h2, add_zero]
  have h1 : (∑ x ∈ range (b + 1), if a ≤ x ∧ x ≤ b then f (x - a) else 0) =
      ∑ x ∈ range (b + 1), if a ≤ x then f (x - a) else 0 := by
    apply sum_congr rfl
    intro x hx
    rw [mem_range] at hx
    have hxb : x ≤ b := by omega
    simp [hxb]
  rw [h1, sum_range_ite_ge a b hab]

lemma choose_div_fact_eq (n k : ℕ) (hk : k ≤ n) :
    (n.choose k : ℂ) / (n.factorial : ℂ) =
      1 / ((k.factorial : ℂ) * ((n - k).factorial : ℂ)) := by
  have h_fact : (n.factorial : ℂ) = (n.choose k : ℂ) * ((k.factorial : ℂ) * ((n - k).factorial : ℂ)) := by
    rw [← mul_assoc]
    exact_mod_cast (Nat.choose_mul_factorial_mul_factorial hk).symm
  have h_ch : (n.choose k : ℂ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hk).ne'
  rw [h_fact, div_mul_eq_div_mul_one_div, div_self h_ch, one_mul]

lemma vandermonde_fact (a b u v : ℕ) (hu : u ≤ a) :
    (if u ≤ b ∧ v ≤ b then
      (b.factorial : ℂ) / ((u.factorial : ℂ) * ((b - u).factorial : ℂ) *
        (v.factorial : ℂ) * ((b - v).factorial : ℂ))
    else 0) =
    ∑ s ∈ range (a + 1),
      if s ≤ u ∧ s ≤ v ∧ u + v - s ≤ b then
        1 / ((s.factorial : ℂ) * ((u - s).factorial : ℂ) *
          ((v - s).factorial : ℂ) * ((b - (u + v - s)).factorial : ℂ))
      else 0 := by
  have h_trunc :
    (∑ s ∈ range (a + 1),
      if s ≤ u ∧ s ≤ v ∧ u + v - s ≤ b then
        1 / ((s.factorial : ℂ) * ((u - s).factorial : ℂ) *
          ((v - s).factorial : ℂ) * ((b - (u + v - s)).factorial : ℂ))
      else 0) =
    ∑ s ∈ range (u + 1),
      if s ≤ v ∧ u + v - s ≤ b then
        1 / ((s.factorial : ℂ) * ((u - s).factorial : ℂ) *
          ((v - s).factorial : ℂ) * ((b - (u + v - s)).factorial : ℂ))
      else 0 := by
    have ha : a + 1 = (u + 1) + (a - u) := by omega
    rw [ha, sum_range_add]
    have h2 : (∑ x ∈ range (a - u),
        if u + 1 + x ≤ u ∧ u + 1 + x ≤ v ∧ u + v - (u + 1 + x) ≤ b then
          1 / (((u + 1 + x).factorial : ℂ) * ((u - (u + 1 + x)).factorial : ℂ) *
            ((v - (u + 1 + x)).factorial : ℂ) * ((b - (u + v - (u + 1 + x))).factorial : ℂ))
        else 0) = 0 := by
      apply sum_eq_zero
      intro x _
      rw [if_neg (by omega)]
    rw [h2, add_zero]
    apply sum_congr rfl
    intro s hs
    rw [mem_range] at hs
    have hsu : s ≤ u := by omega
    simp [hsu]
  rw [h_trunc]
  split_ifs with h
  · rcases h with ⟨hub, hvb⟩
    have hb_eq : (b.factorial : ℂ) / ((u.factorial : ℂ) * ((b - u).factorial : ℂ) *
        (v.factorial : ℂ) * ((b - v).factorial : ℂ)) =
        (b.choose u : ℂ) / ((v.factorial : ℂ) * ((b - v).factorial : ℂ)) := by
      have h_f : (b.factorial : ℂ) = (b.choose u : ℂ) * ((u.factorial : ℂ) * ((b - u).factorial : ℂ)) := by
        rw [← mul_assoc]
        exact_mod_cast (Nat.choose_mul_factorial_mul_factorial hub).symm
      have hu_ne : (u.factorial : ℂ) ≠ 0 := by exact_mod_cast u.factorial_ne_zero
      have hbu_ne : ((b - u).factorial : ℂ) ≠ 0 := by exact_mod_cast (b - u).factorial_ne_zero
      have hv_ne : (v.factorial : ℂ) ≠ 0 := by exact_mod_cast v.factorial_ne_zero
      have hbv_ne : ((b - v).factorial : ℂ) ≠ 0 := by exact_mod_cast (b - v).factorial_ne_zero
      rw [h_f]
      field_simp
    rw [hb_eq]
    have h_v : b = v + (b - v) := (Nat.add_sub_of_le hvb).symm
    have h_van : (b.choose u : ℂ) =
        ∑ s ∈ range (u + 1), (v.choose s : ℂ) * ((b - v).choose (u - s) : ℂ) := by
      have h_nat := Nat.add_choose_eq v (b - v) u
      rw [← h_v] at h_nat
      rw [Nat.sum_antidiagonal_eq_sum_range_succ (fun s t => v.choose s * (b - v).choose t) u] at h_nat
      exact_mod_cast h_nat
    rw [h_van, sum_div]
    apply sum_congr rfl
    intro s hs
    rw [mem_range] at hs
    have hsu : s ≤ u := by omega
    by_cases hsv : s ≤ v ∧ u + v - s ≤ b
    · rw [if_pos hsv]
      have h_ubv : u - s ≤ b - v := by omega
      have h_sub_eq : b - v - (u - s) = b - (u + v - s) := by omega
      have h1 := choose_div_fact_eq v s hsv.1
      have h2 := choose_div_fact_eq (b - v) (u - s) h_ubv
      rw [h_sub_eq] at h2
      calc (v.choose s : ℂ) * ((b - v).choose (u - s) : ℂ) /
            ((v.factorial : ℂ) * ((b - v).factorial : ℂ))
          = ((v.choose s : ℂ) / (v.factorial : ℂ)) *
            (((b - v).choose (u - s) : ℂ) / ((b - v).factorial : ℂ)) := by ring
        _ = _ := by rw [h1, h2]; ring
    · rw [if_neg hsv]
      have h_zero : (v.choose s : ℂ) * ((b - v).choose (u - s) : ℂ) = 0 := by
        by_cases h1 : s ≤ v
        · have h2 : b - v < u - s := by omega
          rw [Nat.choose_eq_zero_of_lt h2]
          simp
        · have h1' : v < s := by omega
          rw [Nat.choose_eq_zero_of_lt h1']
          simp
      rw [h_zero, zero_div]
  · symm
    apply sum_eq_zero
    intro s hs
    rw [mem_range] at hs
    rw [if_neg (by omega)]

lemma sum_bin_div_fact (b : ℕ) (x y : ℂ) :
    (∑ j ∈ range (b + 1), x ^ j * y ^ (b - j) / ((j.factorial : ℂ) * ((b - j).factorial : ℂ))) =
      (x + y) ^ b / (b.factorial : ℂ) := by
  have h_bin : (x + y) ^ b = ∑ j ∈ range (b + 1), (b.choose j : ℂ) * (x ^ j * y ^ (b - j)) := by
    rw [add_pow]
    apply sum_congr rfl
    intro j _
    ring
  rw [h_bin, sum_div]
  apply sum_congr rfl
  intro j hj
  rw [mem_range] at hj
  have hj_le : j ≤ b := Nat.lt_succ_iff.mp hj
  have h_ch : (b.choose j : ℂ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hj_le).ne'
  have h_fact : (b.factorial : ℂ) = (b.choose j : ℂ) * ((j.factorial : ℂ) * ((b - j).factorial : ℂ)) := by
    rw [← mul_assoc]
    exact_mod_cast (Nat.choose_mul_factorial_mul_factorial hj_le).symm
  rw [h_fact, mul_div_mul_left _ _ h_ch]

lemma sum_alt_div_fact (b : ℕ) :
    (∑ j ∈ range (b + 1), (-1 : ℂ) ^ (b - j) / ((j.factorial : ℂ) * ((b - j).factorial : ℂ))) =
      if b = 0 then 1 else 0 := by
  have h := sum_bin_div_fact b 1 (-1)
  simp only [one_pow, one_mul, add_neg_cancel] at h
  rw [h]
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · simp
  · rw [ if_neg hb.ne', zero_pow hb.ne', zero_div]

lemma sum_range_min {α : Type*} [AddCommMonoid α] (n b : ℕ) (f : ℕ → α) :
    (∑ j ∈ range (min n b + 1), f j) =
      ∑ j ∈ range (b + 1), if j ≤ n then f j else 0 := by
  rw [sum_ite]
  have h_filter : (filter (fun j => j ≤ n) (range (b + 1))) = range (min n b + 1) := by
    ext j
    simp only [mem_filter, mem_range]
    omega
  rw [h_filter, sum_const_zero, add_zero]

lemma cexp_hasSum (z : ℂ) : HasSum (fun n : ℕ => z ^ n / (n.factorial : ℂ)) (Complex.exp z) := by
  rw [Complex.exp_eq_exp_ℂ]
  exact NormedSpace.expSeries_div_hasSum_exp z

lemma rexp_hasSum (x : ℝ) : HasSum (fun n : ℕ => x ^ n / (n.factorial : ℝ)) (Real.exp x) := by
  rw [Real.exp_eq_exp_ℝ]
  exact NormedSpace.expSeries_div_hasSum_exp x

lemma hasSum_ite_le (k : ℕ) (h : ℕ → ℂ) {g : ℂ} (H : HasSum h g) :
    HasSum (fun n : ℕ => if k ≤ n then h (n - k) else 0) g := by
  have h_add : HasSum (fun n => (if k ≤ n + k then h (n + k - k) else (0 : ℂ))) g := by
    have h_eq : (fun n => (if k ≤ n + k then h (n + k - k) else (0 : ℂ))) = h := by
      funext n
      have hk : k ≤ n + k := Nat.le_add_left k n
      have hsub : n + k - k = n := Nat.add_sub_cancel n k
      simp only [hk, hsub, ↓reduceIte]
    rw [h_eq]
    exact H
  have h_shift := (hasSum_nat_add_iff (f := fun n => if k ≤ n then h (n - k) else 0) k).mp h_add
  have h_sum_zero : (∑ i ∈ range k, (if k ≤ i then h (i - k) else (0 : ℂ))) = 0 := by
    apply sum_eq_zero
    intro i hi
    rw [mem_range] at hi
    rw [if_neg (by omega)]
  rw [h_sum_zero, add_zero] at h_shift
  exact h_shift

lemma hasSum_ite_le_real (k : ℕ) (h : ℕ → ℝ) {g : ℝ} (H : HasSum h g) :
    HasSum (fun n : ℕ => if k ≤ n then h (n - k) else 0) g := by
  have h_add : HasSum (fun n => (if k ≤ n + k then h (n + k - k) else (0 : ℝ))) g := by
    have h_eq : (fun n => (if k ≤ n + k then h (n + k - k) else (0 : ℝ))) = h := by
      funext n
      have hk : k ≤ n + k := Nat.le_add_left k n
      have hsub : n + k - k = n := Nat.add_sub_cancel n k
      simp only [hk, hsub, ↓reduceIte]
    rw [h_eq]
    exact H
  have h_shift := (hasSum_nat_add_iff (f := fun n => if k ≤ n then h (n - k) else 0) k).mp h_add
  have h_sum_zero : (∑ i ∈ range k, (if k ≤ i then h (i - k) else (0 : ℝ))) = 0 := by
    apply sum_eq_zero
    intro i hi
    rw [mem_range] at hi
    rw [if_neg (by omega)]
  rw [h_sum_zero, add_zero] at h_shift
  exact h_shift

lemma master_pow_eq (ξ : ℝ) (z : ℂ) (a j u v s b : ℕ)
    (hu : u ≤ a) (hv : v ≤ j) (hsu : s ≤ u) (hsv : s ≤ v) (hb : u + v - s ≤ b) :
    (ξ : ℂ) ^ b * (((ξ : ℂ) * z) ^ (b - u) * (-star ((ξ : ℂ) * z)) ^ (a - u)) *
      ((star z) ^ (b - v) * (-z) ^ (j - v)) =
    ((ξ : ℂ) ^ a * z ^ (j - s) * (star z) ^ (a - s) *
      (-1 : ℂ) ^ (a - u) * (((ξ ^ 2 : ℝ) : ℂ)) ^ (v - s) * (-1 : ℂ) ^ (j - v)) *
      (((ξ ^ 2 * Complex.normSq z : ℝ) : ℂ)) ^ (b - (u + v - s)) := by
  let d := b - (u + v - s)
  have hb_eq : b = (u - s) + (v - s) + s + d := by omega
  have hbu_eq : b - u = (v - s) + d := by omega
  have hbv_eq : b - v = (u - s) + d := by omega
  have ha_eq : a = (a - u) + (u - s) + s := by omega
  have hj_eq : j - s = (v - s) + (j - v) := by omega
  have has_eq : a - s = (a - u) + (u - s) := by omega
  have h_star_xiz : -star ((ξ : ℂ) * z) = (-1 : ℂ) * (ξ : ℂ) * star z := by
    simp only [star_mul', Complex.star_def, Complex.conj_ofReal]
    ring
  have h_neg_z : -z = (-1 : ℂ) * z := by ring
  have h_norm : (((ξ ^ 2 * Complex.normSq z : ℝ) : ℂ)) = (ξ : ℂ) * (ξ : ℂ) * z * star z := by
    rw [Complex.ofReal_mul, Complex.ofReal_pow, Complex.normSq_eq_conj_mul_self, Complex.star_def]
    ring
  rw [h_star_xiz, h_neg_z, h_norm]
  change (ξ : ℂ) ^ b * (((ξ : ℂ) * z) ^ (b - u) * ((-1 : ℂ) * (ξ : ℂ) * star z) ^ (a - u)) *
      (star z ^ (b - v) * ((-1 : ℂ) * z) ^ (j - v)) =
    (ξ : ℂ) ^ a * z ^ (j - s) * star z ^ (a - s) * (-1 : ℂ) ^ (a - u) *
      (((ξ ^ 2 : ℝ) : ℂ)) ^ (v - s) * (-1 : ℂ) ^ (j - v) *
      ((ξ : ℂ) * (ξ : ℂ) * z * star z) ^ d
  have h_xia : (ξ : ℂ) ^ a = (ξ : ℂ) ^ ((a - u) + (u - s) + s) := by rw [← ha_eq]
  push_cast
  rw [hbu_eq, hbv_eq, hb_eq, hj_eq, has_eq, h_xia]
  simp only [pow_add, mul_pow, sq]
  ring

def masterCoeff (ξ : ℝ) (z : ℂ) (a j u v s : ℕ) : ℂ :=
  ((ξ : ℂ) ^ a * z ^ (j - s) * (star z) ^ (a - s) / (s.factorial : ℂ)) *
  ((-1 : ℂ) ^ (a - u) / (((u - s).factorial : ℂ) * ((a - u).factorial : ℂ))) *
  ((((ξ ^ 2 : ℝ) : ℂ)) ^ (v - s) * (-1 : ℂ) ^ (j - v) /
    (((v - s).factorial : ℂ) * ((j - v).factorial : ℂ)))

lemma disp_star_eq (z : ℂ) (b j : ℕ) :
    star (displacementMatrix z b j) =
      (((Real.exp (-Complex.normSq z / 2) *
        Real.sqrt ((b.factorial : ℝ) * (j.factorial : ℝ)) : ℝ) : ℂ)) *
        ∑ v ∈ range (j + 1),
          if v ≤ b then
            (star z) ^ (b - v) * (-z) ^ (j - v) /
              ((v.factorial : ℂ) * ((b - v).factorial : ℂ) * ((j - v).factorial : ℂ))
          else 0 := by
  dsimp only [displacementMatrix]
  rw [sum_range_min, star_mul', Complex.star_def, Complex.conj_ofReal, map_sum]
  congr 1
  apply sum_congr rfl
  intro v _
  split_ifs with hv
  · simp only [map_div₀, map_mul, map_pow, map_neg, Complex.conj_conj, Complex.conj_natCast]
  · simp

lemma master_summand_eq (ξ : ℝ) (z : ℂ) (a j b : ℕ) :
    (ξ : ℂ) ^ b * displacementMatrix ((ξ : ℂ) * z) b a * star (displacementMatrix z b j) =
      (((Real.exp (-(1 + ξ ^ 2) * Complex.normSq z / 2) *
        Real.sqrt ((a.factorial : ℝ) * (j.factorial : ℝ)) : ℝ) : ℂ)) *
        ∑ u ∈ range (a + 1), ∑ v ∈ range (j + 1), ∑ s ∈ range (a + 1),
          if s ≤ u ∧ s ≤ v then
            if u + v - s ≤ b then
              masterCoeff ξ z a j u v s *
                ((((ξ ^ 2 * Complex.normSq z : ℝ) : ℂ)) ^ (b - (u + v - s)) /
                  (((b - (u + v - s)).factorial : ℂ)))
            else 0
          else 0 := by
  rw [disp_star_eq z b j]
  dsimp only [displacementMatrix]
  rw [sum_range_min b a]
  have h_pref :
    ((Real.exp (-Complex.normSq ((ξ : ℂ) * z) / 2) *
      Real.sqrt ((b.factorial : ℝ) * (a.factorial : ℝ))) : ℝ) *
    ((Real.exp (-Complex.normSq z / 2) *
      Real.sqrt ((b.factorial : ℝ) * (j.factorial : ℝ))) : ℝ) =
    (Real.exp (-(1 + ξ ^ 2) * Complex.normSq z / 2) *
      Real.sqrt ((a.factorial : ℝ) * (j.factorial : ℝ))) * (b.factorial : ℝ) := by
    have h_nsq : Complex.normSq ((ξ : ℂ) * z) = ξ ^ 2 * Complex.normSq z := by
      rw [Complex.normSq_mul, Complex.normSq_ofReal, sq]
    have h_exp : Real.exp (-(ξ ^ 2 * Complex.normSq z) / 2) * Real.exp (-Complex.normSq z / 2) =
        Real.exp (-(1 + ξ ^ 2) * Complex.normSq z / 2) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have h_sqrt : Real.sqrt ((b.factorial : ℝ) * (a.factorial : ℝ)) *
        Real.sqrt ((b.factorial : ℝ) * (j.factorial : ℝ)) =
        (b.factorial : ℝ) * Real.sqrt ((a.factorial : ℝ) * (j.factorial : ℝ)) := by
      rw [Real.sqrt_mul (by positivity) (a.factorial : ℝ),
        Real.sqrt_mul (by positivity) (j.factorial : ℝ),
        Real.sqrt_mul (by positivity) (j.factorial : ℝ)]
      calc Real.sqrt (b.factorial : ℝ) * Real.sqrt (a.factorial : ℝ) *
            (Real.sqrt (b.factorial : ℝ) * Real.sqrt (j.factorial : ℝ))
          = (Real.sqrt (b.factorial : ℝ) * Real.sqrt (b.factorial : ℝ)) *
            (Real.sqrt (a.factorial : ℝ) * Real.sqrt (j.factorial : ℝ)) := by ring
        _ = (b.factorial : ℝ) * (Real.sqrt (a.factorial : ℝ) * Real.sqrt (j.factorial : ℝ)) := by
            rw [Real.mul_self_sqrt (by positivity)]
    rw [h_nsq]
    calc (Real.exp (-(ξ ^ 2 * Complex.normSq z) / 2) *
          Real.sqrt ((b.factorial : ℝ) * (a.factorial : ℝ))) *
         (Real.exp (-Complex.normSq z / 2) *
          Real.sqrt ((b.factorial : ℝ) * (j.factorial : ℝ)))
        = (Real.exp (-(ξ ^ 2 * Complex.normSq z) / 2) * Real.exp (-Complex.normSq z / 2)) *
          (Real.sqrt ((b.factorial : ℝ) * (a.factorial : ℝ)) *
           Real.sqrt ((b.factorial : ℝ) * (j.factorial : ℝ))) := by ring
      _ = _ := by rw [h_exp, h_sqrt]; ring
  have h_rearrange : ∀ (P1 P2 S1 S2 : ℂ),
      (ξ : ℂ) ^ b * (P1 * S1) * (P2 * S2) = (P1 * P2) * ((ξ : ℂ) ^ b * (S1 * S2)) := by
    intros; ring
  rw [h_rearrange, ← Complex.ofReal_mul, h_pref, Complex.ofReal_mul, Complex.ofReal_natCast, mul_assoc]
  congr 1
  rw [sum_mul, mul_sum, mul_sum]
  have h_sum2 : ∀ u ∈ range (a + 1),
      (b.factorial : ℂ) * ((ξ : ℂ) ^ b *
        ((if u ≤ b then
            ((ξ : ℂ) * z) ^ (b - u) * (-star ((ξ : ℂ) * z)) ^ (a - u) /
              ((u.factorial : ℂ) * ((b - u).factorial : ℂ) * ((a - u).factorial : ℂ))
          else 0) *
        ∑ v ∈ range (j + 1),
          if v ≤ b then
            (star z) ^ (b - v) * (-z) ^ (j - v) /
              ((v.factorial : ℂ) * ((b - v).factorial : ℂ) * ((j - v).factorial : ℂ))
          else 0)) =
      ∑ v ∈ range (j + 1), ∑ s ∈ range (a + 1),
        if s ≤ u ∧ s ≤ v then
          if u + v - s ≤ b then
            masterCoeff ξ z a j u v s *
              ((((ξ ^ 2 * Complex.normSq z : ℝ) : ℂ)) ^ (b - (u + v - s)) /
                (((b - (u + v - s)).factorial : ℂ)))
          else 0
        else 0 := by
    intro u hu
    rw [mem_range] at hu
    have hua : u ≤ a := by omega
    rw [mul_sum, mul_sum, mul_sum]
    apply sum_congr rfl
    intro v hv
    rw [mem_range] at hv
    have hvj : v ≤ j := by omega
    have h_ite_prod :
      (b.factorial : ℂ) * ((ξ : ℂ) ^ b *
        ((if u ≤ b then
            ((ξ : ℂ) * z) ^ (b - u) * (-star ((ξ : ℂ) * z)) ^ (a - u) /
              ((u.factorial : ℂ) * ((b - u).factorial : ℂ) * ((a - u).factorial : ℂ))
          else 0) *
         (if v ≤ b then
            (star z) ^ (b - v) * (-z) ^ (j - v) /
              ((v.factorial : ℂ) * ((b - v).factorial : ℂ) * ((j - v).factorial : ℂ))
          else 0))) =
      (if u ≤ b ∧ v ≤ b then
        (b.factorial : ℂ) / ((u.factorial : ℂ) * ((b - u).factorial : ℂ) *
          (v.factorial : ℂ) * ((b - v).factorial : ℂ))
      else 0) *
      ((ξ : ℂ) ^ b * (((ξ : ℂ) * z) ^ (b - u) * (-star ((ξ : ℂ) * z)) ^ (a - u)) *
        ((star z) ^ (b - v) * (-z) ^ (j - v)) /
        (((a - u).factorial : ℂ) * ((j - v).factorial : ℂ))) := by
      by_cases hub : u ≤ b
      · by_cases hvb : v ≤ b
        · simp only [hub, hvb, and_self, ↓reduceIte]
          ring
        · simp [hub, hvb]
      · simp [hub]
    rw [h_ite_prod, vandermonde_fact a b u v hua, sum_mul]
    apply sum_congr rfl
    intro s _
    by_cases hsv : s ≤ u ∧ s ≤ v
    · by_cases hb_le : u + v - s ≤ b
      · have h_all : s ≤ u ∧ s ≤ v ∧ u + v - s ≤ b := ⟨hsv.1, hsv.2, hb_le⟩
        rw [if_pos h_all, if_pos hsv, if_pos hb_le]
        rw [master_pow_eq ξ z a j u v s b hua hvj hsv.1 hsv.2 hb_le]
        dsimp only [masterCoeff]
        ring
      · have h_not : ¬ (s ≤ u ∧ s ≤ v ∧ u + v - s ≤ b) := by omega
        rw [if_neg h_not, if_pos hsv, if_neg hb_le, zero_mul]
    · have h_not : ¬ (s ≤ u ∧ s ≤ v ∧ u + v - s ≤ b) := by omega
      rw [if_neg h_not, if_neg hsv, zero_mul]
  exact sum_congr rfl h_sum2

lemma master_finite_sum_eq (ξ : ℝ) (z : ℂ) (a j : ℕ) :
    (∑ u ∈ range (a + 1), ∑ v ∈ range (j + 1), ∑ s ∈ range (a + 1),
      if s ≤ u ∧ s ≤ v then masterCoeff ξ z a j u v s else 0) =
    if a ≤ j then
      (ξ : ℂ) ^ a * ((((ξ ^ 2 - 1 : ℝ) : ℂ) * z) ^ (j - a) /
        ((a.factorial : ℂ) * ((j - a).factorial : ℂ)))
    else 0 := by
  have h_swap0 :
    (∑ u ∈ range (a + 1), ∑ v ∈ range (j + 1), ∑ s ∈ range (a + 1),
      if s ≤ u ∧ s ≤ v then masterCoeff ξ z a j u v s else 0) =
    ∑ u ∈ range (a + 1), ∑ s ∈ range (a + 1), ∑ v ∈ range (j + 1),
      if s ≤ u ∧ s ≤ v then masterCoeff ξ z a j u v s else 0 := by
    apply sum_congr rfl
    intro u _
    rw [sum_comm]
  rw [h_swap0, sum_comm]
  have h_inner : ∀ s ∈ range (a + 1),
    (∑ u ∈ range (a + 1), ∑ v ∈ range (j + 1),
      if s ≤ u ∧ s ≤ v then masterCoeff ξ z a j u v s else 0) =
    if s = a then
      if a ≤ j then
        (ξ : ℂ) ^ a * ((((ξ ^ 2 - 1 : ℝ) : ℂ) * z) ^ (j - a) /
          ((a.factorial : ℂ) * ((j - a).factorial : ℂ)))
      else 0
    else 0 := by
    intro s hs
    rw [mem_range] at hs
    have hsa : s ≤ a := by omega
    have h_prod :
      (∑ u ∈ range (a + 1), ∑ v ∈ range (j + 1),
        if s ≤ u ∧ s ≤ v then masterCoeff ξ z a j u v s else 0) =
      ((ξ : ℂ) ^ a * z ^ (j - s) * (star z) ^ (a - s) / (s.factorial : ℂ)) *
      ((∑ u ∈ range (a + 1),
        if s ≤ u then (-1 : ℂ) ^ (a - u) / (((u - s).factorial : ℂ) * ((a - u).factorial : ℂ)) else 0) *
      (∑ v ∈ range (j + 1),
        if s ≤ v then (((ξ ^ 2 : ℝ) : ℂ)) ^ (v - s) * (-1 : ℂ) ^ (j - v) /
          (((v - s).factorial : ℂ) * ((j - v).factorial : ℂ)) else 0)) := by
      rw [sum_mul_sum, mul_sum]
      apply sum_congr rfl
      intro u _
      rw [mul_sum]
      apply sum_congr rfl
      intro v _
      by_cases hsu : s ≤ u
      · by_cases hsv : s ≤ v
        · simp only [hsu, hsv, and_self, ↓reduceIte, masterCoeff]
          ring
        · simp [hsu, hsv]
      · simp [hsu]
    rw [h_prod]
    have h_u :
      (∑ u ∈ range (a + 1),
        if s ≤ u then (-1 : ℂ) ^ (a - u) / (((u - s).factorial : ℂ) * ((a - u).factorial : ℂ)) else 0) =
      if s = a then 1 else 0 := by
      let fu : ℕ → ℂ := fun k => (-1 : ℂ) ^ ((a - s) - k) / ((k.factorial : ℂ) * (((a - s) - k).factorial : ℂ))
      have h_u_eq :
        (∑ u ∈ range (a + 1),
          if s ≤ u then (-1 : ℂ) ^ (a - u) / (((u - s).factorial : ℂ) * ((a - u).factorial : ℂ)) else 0) =
        ∑ u ∈ range (a + 1), if s ≤ u then fu (u - s) else 0 := by
        apply sum_congr rfl
        intro u _
        split_ifs with hsu
        · dsimp [fu]
          have : a - u = (a - s) - (u - s) := by omega
          rw [this]
        · rfl
      rw [h_u_eq, sum_range_ite_ge s a hsa fu, sum_alt_div_fact (a - s)]
      have : (a - s = 0) ↔ (s = a) := by omega
      simp [this]
    rw [h_u]
    by_cases hsa_eq : s = a
    · subst s
      simp only [↓reduceIte, one_mul, Nat.sub_self, pow_zero]
      by_cases haj : a ≤ j
      · rw [if_pos haj]
        let fv : ℕ → ℂ := fun k => (((ξ ^ 2 : ℝ) : ℂ)) ^ k * (-1 : ℂ) ^ ((j - a) - k) /
          ((k.factorial : ℂ) * (((j - a) - k).factorial : ℂ))
        have h_v_eq :
          (∑ v ∈ range (j + 1),
            if a ≤ v then (((ξ ^ 2 : ℝ) : ℂ)) ^ (v - a) * (-1 : ℂ) ^ (j - v) /
              (((v - a).factorial : ℂ) * ((j - v).factorial : ℂ)) else 0) =
          ∑ v ∈ range (j + 1), if a ≤ v then fv (v - a) else 0 := by
          apply sum_congr rfl
          intro v _
          split_ifs with hav
          · dsimp [fv]
            have : j - v = (j - a) - (v - a) := by omega
            rw [this]
          · rfl
        rw [h_v_eq, sum_range_ite_ge a j haj fv, sum_bin_div_fact (j - a) ((ξ ^ 2 : ℝ) : ℂ) (-1)]
        have h_sub : (((ξ ^ 2 : ℝ) : ℂ) + -1) = ((ξ ^ 2 - 1 : ℝ) : ℂ) := by push_cast; ring
        rw [h_sub, mul_pow]
        ring
      · rw [if_neg haj]
        have h_v_zero :
          (∑ v ∈ range (j + 1),
            if a ≤ v then (((ξ ^ 2 : ℝ) : ℂ)) ^ (v - a) * (-1 : ℂ) ^ (j - v) /
              (((v - a).factorial : ℂ) * ((j - v).factorial : ℂ)) else 0) = 0 := by
          apply sum_eq_zero
          intro v hv
          rw [mem_range] at hv
          rw [if_neg (by omega)]
        rw [h_v_zero, mul_zero]
    · simp [hsa_eq]
  rw [sum_congr rfl h_inner, sum_ite_eq', if_pos (mem_range.mpr (Nat.lt_succ_self a))]

lemma hasSum_xi_disp_mul (ξ : ℝ) (z : ℂ) (a j : ℕ) :
    HasSum (fun b : ℕ => (ξ : ℂ) ^ b * displacementMatrix ((ξ : ℂ) * z) b a * star (displacementMatrix z b j))
      (if a ≤ j then
        (((Real.exp (-(1 - ξ ^ 2) * Complex.normSq z / 2) *
          Real.sqrt (j.choose a : ℝ) * ξ ^ a : ℝ) : ℂ)) *
        ((((ξ ^ 2 - 1 : ℝ) : ℂ) * z) ^ (j - a) / (Real.sqrt ((j - a).factorial : ℝ) : ℂ))
      else 0) := by
  have h_fun :
    (fun b : ℕ => (ξ : ℂ) ^ b * displacementMatrix ((ξ : ℂ) * z) b a * star (displacementMatrix z b j)) =
    fun b : ℕ =>
      (((Real.exp (-(1 + ξ ^ 2) * Complex.normSq z / 2) *
        Real.sqrt ((a.factorial : ℝ) * (j.factorial : ℝ)) : ℝ) : ℂ)) *
        ∑ u ∈ range (a + 1), ∑ v ∈ range (j + 1), ∑ s ∈ range (a + 1),
          if s ≤ u ∧ s ≤ v then
            if u + v - s ≤ b then
              masterCoeff ξ z a j u v s *
                ((((ξ ^ 2 * Complex.normSq z : ℝ) : ℂ)) ^ (b - (u + v - s)) /
                  (((b - (u + v - s)).factorial : ℂ)))
            else 0
          else 0 := funext (master_summand_eq ξ z a j)
  rw [h_fun]
  let E : ℂ := ((Real.exp (ξ ^ 2 * Complex.normSq z) : ℝ) : ℂ)
  have h_exp_s : HasSum (fun d : ℕ => (((ξ ^ 2 * Complex.normSq z : ℝ) : ℂ)) ^ d / (d.factorial : ℂ)) E := by
    dsimp [E]
    rw [Complex.ofReal_exp]
    exact cexp_hasSum (((ξ ^ 2 * Complex.normSq z : ℝ) : ℂ))
  have h_s : ∀ u ∈ range (a + 1), ∀ v ∈ range (j + 1), ∀ s ∈ range (a + 1),
      HasSum (fun b : ℕ =>
        if s ≤ u ∧ s ≤ v then
          if u + v - s ≤ b then
            masterCoeff ξ z a j u v s *
              ((((ξ ^ 2 * Complex.normSq z : ℝ) : ℂ)) ^ (b - (u + v - s)) /
                (((b - (u + v - s)).factorial : ℂ)))
          else 0
        else 0)
        ((if s ≤ u ∧ s ≤ v then masterCoeff ξ z a j u v s else 0) * E) := by
    intro u _ v _ s _
    by_cases hsv : s ≤ u ∧ s ≤ v
    · have h_fn :
        (fun b : ℕ =>
          if s ≤ u ∧ s ≤ v then
            if u + v - s ≤ b then
              masterCoeff ξ z a j u v s *
                ((((ξ ^ 2 * Complex.normSq z : ℝ) : ℂ)) ^ (b - (u + v - s)) /
                  (((b - (u + v - s)).factorial : ℂ)))
            else 0
          else 0) =
        fun b : ℕ =>
          if u + v - s ≤ b then
            masterCoeff ξ z a j u v s *
              ((((ξ ^ 2 * Complex.normSq z : ℝ) : ℂ)) ^ (b - (u + v - s)) /
                (((b - (u + v - s)).factorial : ℂ)))
          else 0 := by
        funext b
        rw [if_pos hsv]
      rw [h_fn, if_pos hsv]
      exact hasSum_ite_le (u + v - s)
        (fun d => masterCoeff ξ z a j u v s *
          ((((ξ ^ 2 * Complex.normSq z : ℝ) : ℂ)) ^ d / (d.factorial : ℂ)))
        (h_exp_s.mul_left (masterCoeff ξ z a j u v s))
    · have h_fn :
        (fun b : ℕ =>
          if s ≤ u ∧ s ≤ v then
            if u + v - s ≤ b then
              masterCoeff ξ z a j u v s *
                ((((ξ ^ 2 * Complex.normSq z : ℝ) : ℂ)) ^ (b - (u + v - s)) /
                  (((b - (u + v - s)).factorial : ℂ)))
            else 0
          else 0) = fun _ => 0 := by
        funext b
        rw [if_neg hsv]
      rw [h_fn, if_neg hsv, zero_mul]
      exact hasSum_zero
  have h_sum3 : HasSum (fun b : ℕ =>
      ∑ u ∈ range (a + 1), ∑ v ∈ range (j + 1), ∑ s ∈ range (a + 1),
        if s ≤ u ∧ s ≤ v then
          if u + v - s ≤ b then
            masterCoeff ξ z a j u v s *
              ((((ξ ^ 2 * Complex.normSq z : ℝ) : ℂ)) ^ (b - (u + v - s)) /
                (((b - (u + v - s)).factorial : ℂ)))
          else 0
        else 0)
      (∑ u ∈ range (a + 1), ∑ v ∈ range (j + 1), ∑ s ∈ range (a + 1),
        (if s ≤ u ∧ s ≤ v then masterCoeff ξ z a j u v s else 0) * E) :=
    hasSum_sum (fun u hu => hasSum_sum (fun v hv => hasSum_sum (fun s hs => h_s u hu v hv s hs)))
  have h_all := h_sum3.mul_left (((Real.exp (-(1 + ξ ^ 2) * Complex.normSq z / 2) *
    Real.sqrt ((a.factorial : ℝ) * (j.factorial : ℝ)) : ℝ) : ℂ))
  have h_factor_E :
    (∑ u ∈ range (a + 1), ∑ v ∈ range (j + 1), ∑ s ∈ range (a + 1),
      (if s ≤ u ∧ s ≤ v then masterCoeff ξ z a j u v s else 0) * E) =
    (∑ u ∈ range (a + 1), ∑ v ∈ range (j + 1), ∑ s ∈ range (a + 1),
      if s ≤ u ∧ s ≤ v then masterCoeff ξ z a j u v s else 0) * E := by
    simp_rw [← sum_mul]
  rw [h_factor_E, master_finite_sum_eq] at h_all
  suffices h_eq :
    (((Real.exp (-(1 + ξ ^ 2) * Complex.normSq z / 2) *
      Real.sqrt ((a.factorial : ℝ) * (j.factorial : ℝ)) : ℝ) : ℂ)) *
      ((if a ≤ j then
          (ξ : ℂ) ^ a * ((((ξ ^ 2 - 1 : ℝ) : ℂ) * z) ^ (j - a) /
            ((a.factorial : ℂ) * ((j - a).factorial : ℂ)))
        else 0) * E) =
    if a ≤ j then
      (((Real.exp (-(1 - ξ ^ 2) * Complex.normSq z / 2) *
        Real.sqrt (j.choose a : ℝ) * ξ ^ a : ℝ) : ℂ)) *
      ((((ξ ^ 2 - 1 : ℝ) : ℂ) * z) ^ (j - a) / (Real.sqrt ((j - a).factorial : ℝ) : ℂ))
    else 0 by
    rwa [h_eq] at h_all
  split_ifs with haj
  · dsimp only [E]
    have h_exp : Real.exp (-(1 + ξ ^ 2) * Complex.normSq z / 2) * Real.exp (ξ ^ 2 * Complex.normSq z) =
        Real.exp (-(1 - ξ ^ 2) * Complex.normSq z / 2) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have h_ch : Real.sqrt ((a.factorial : ℝ) * (j.factorial : ℝ)) /
        ((a.factorial : ℝ) * ((j - a).factorial : ℝ)) =
        Real.sqrt (j.choose a : ℝ) / Real.sqrt ((j - a).factorial : ℝ) := by
      have h_jf : (j.factorial : ℝ) = (j.choose a : ℝ) * (a.factorial : ℝ) * ((j - a).factorial : ℝ) := by
        exact_mod_cast (Nat.choose_mul_factorial_mul_factorial haj).symm
      have ha_pos : (0 : ℝ) < a.factorial := by exact_mod_cast a.factorial_pos
      have hja_pos : (0 : ℝ) < (j - a).factorial := by exact_mod_cast (j - a).factorial_pos
      have h_sq_a : Real.sqrt (a.factorial : ℝ) * Real.sqrt (a.factorial : ℝ) = (a.factorial : ℝ) :=
        Real.mul_self_sqrt ha_pos.le
      have h_sq_ja : Real.sqrt ((j - a).factorial : ℝ) * Real.sqrt ((j - a).factorial : ℝ) = ((j - a).factorial : ℝ) :=
        Real.mul_self_sqrt hja_pos.le
      have h_lhs_sqrt : Real.sqrt ((a.factorial : ℝ) * (j.factorial : ℝ)) =
          Real.sqrt (j.choose a : ℝ) * (a.factorial : ℝ) * Real.sqrt ((j - a).factorial : ℝ) := by
        rw [h_jf]
        have : (a.factorial : ℝ) * ((j.choose a : ℝ) * (a.factorial : ℝ) * ((j - a).factorial : ℝ)) =
            (j.choose a : ℝ) * ((a.factorial : ℝ) * (a.factorial : ℝ)) * ((j - a).factorial : ℝ) := by ring
        rw [this, Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity),
          Real.sqrt_mul_self ha_pos.le]
      rw [h_lhs_sqrt]
      conv_lhs => rhs; rw [← h_sq_ja]
      have ha_ne : (a.factorial : ℝ) ≠ 0 := ha_pos.ne'
      have hja_s_ne : Real.sqrt ((j - a).factorial : ℝ) ≠ 0 := (Real.sqrt_pos.2 hja_pos).ne'
      field_simp
    have h_ch_c : ((Real.sqrt ((a.factorial : ℝ) * (j.factorial : ℝ)) : ℝ) : ℂ) /
        ((a.factorial : ℂ) * ((j - a).factorial : ℂ)) =
        (Real.sqrt (j.choose a : ℝ) : ℂ) / (Real.sqrt ((j - a).factorial : ℝ) : ℂ) := by
      exact_mod_cast h_ch
    have h_exp_c : ((Real.exp (-(1 + ξ ^ 2) * Complex.normSq z / 2) : ℝ) : ℂ) *
        ((Real.exp (ξ ^ 2 * Complex.normSq z) : ℝ) : ℂ) =
        ((Real.exp (-(1 - ξ ^ 2) * Complex.normSq z / 2) : ℝ) : ℂ) := by
      exact_mod_cast h_exp
    have h_rhs_cast : ((Real.exp (-(1 - ξ ^ 2) * Complex.normSq z / 2) *
        Real.sqrt (j.choose a : ℝ) * ξ ^ a : ℝ) : ℂ) =
      ((Real.exp (-(1 - ξ ^ 2) * Complex.normSq z / 2) : ℝ) : ℂ) *
      (Real.sqrt (j.choose a : ℝ) : ℂ) * (ξ : ℂ) ^ a := by
      rw [Complex.ofReal_mul, Complex.ofReal_mul, Complex.ofReal_pow]
    rw [Complex.ofReal_mul (Real.exp (-(1 + ξ ^ 2) * Complex.normSq z / 2)), h_rhs_cast]
    calc (((Real.exp (-(1 + ξ ^ 2) * Complex.normSq z / 2) : ℝ) : ℂ) *
            ((Real.sqrt ((a.factorial : ℝ) * (j.factorial : ℝ)) : ℝ) : ℂ)) *
          ((ξ : ℂ) ^ a * (((((ξ ^ 2 - 1 : ℝ) : ℂ) * z) ^ (j - a) /
            ((a.factorial : ℂ) * ((j - a).factorial : ℂ)))) *
          ((Real.exp (ξ ^ 2 * Complex.normSq z) : ℝ) : ℂ))
        = ((((Real.exp (-(1 + ξ ^ 2) * Complex.normSq z / 2) : ℝ) : ℂ) *
            ((Real.exp (ξ ^ 2 * Complex.normSq z) : ℝ) : ℂ)) *
           ((((Real.sqrt ((a.factorial : ℝ) * (j.factorial : ℝ)) : ℝ) : ℂ) /
            ((a.factorial : ℂ) * ((j - a).factorial : ℂ)))) *
           (ξ : ℂ) ^ a * ((((ξ ^ 2 - 1 : ℝ) : ℂ) * z) ^ (j - a))) := by ring
      _ = _ := by
          rw [h_exp_c, h_ch_c]
          ring
  · ring

lemma hasSum_disp_col_ortho (z : ℂ) (a j : ℕ) :
    HasSum (fun b : ℕ => displacementMatrix z b a * star (displacementMatrix z b j))
      (if a = j then 1 else 0) := by
  have h := hasSum_xi_disp_mul 1 z a j
  have h_fn :
    (fun b : ℕ => (((1 : ℝ) : ℂ)) ^ b * displacementMatrix (((1 : ℝ) : ℂ) * z) b a * star (displacementMatrix z b j)) =
    (fun b : ℕ => displacementMatrix z b a * star (displacementMatrix z b j)) := by
    funext b
    simp
  rw [h_fn] at h
  suffices h_eq :
    (if a ≤ j then
      (((Real.exp (-(1 - (1 : ℝ) ^ 2) * Complex.normSq z / 2) *
        Real.sqrt (j.choose a : ℝ) * (1 : ℝ) ^ a : ℝ) : ℂ)) *
      (((((1 : ℝ) ^ 2 - 1 : ℝ) : ℂ) * z) ^ (j - a) / (Real.sqrt ((j - a).factorial : ℝ) : ℂ))
    else 0) = if a = j then 1 else 0 by
    rwa [h_eq] at h
  by_cases haj : a = j
  · subst haj
    simp
  · rw [if_neg haj]
    split_ifs with hle
    · have hsub : j - a ≠ 0 := by omega
      have hzero : (((((1 : ℝ) ^ 2 - 1 : ℝ) : ℂ) * z)) ^ (j - a) = 0 := by
        have : ((((1 : ℝ) ^ 2 - 1 : ℝ) : ℂ) * z) = 0 := by norm_num
        rw [this, zero_pow hsub]
      rw [hzero, zero_div, mul_zero]
    · rfl

lemma sum_range_sub_eq_sum_range_add {α : Type*} [AddCommMonoid α] (j u : ℕ) (hu : u ≤ j) (G : ℕ → α) :
    (∑ p ∈ range (j + 1), if u ≤ p then G (p - u) else 0) =
      ∑ v ∈ range (j + 1), if u + v ≤ j then G v else 0 := by
  rw [sum_range_ite_ge u j hu G]
  have h := sum_range_ite_interval j 0 (j - u) (Nat.zero_le _) (Nat.sub_le j u) G
  simp only [zero_le, true_and, Nat.sub_zero] at h
  rw [← h]
  apply sum_congr rfl
  intro v _
  have : (v ≤ j - u) ↔ (u + v ≤ j) := by omega
  simp [this]

def bcoef (η : ℝ) (ell m : ℕ) : ℝ :=
  Real.sqrt (Nat.choose (m + ell) ell : ℝ) * Real.sqrt η ^ m * Real.sqrt (1 - η) ^ ell

def lcoefX (e : ℝ) (m n l : ℕ) : ℝ :=
  Real.sqrt (Nat.choose (m + l) l : ℝ) * Real.sqrt (Nat.choose (n + l) l : ℝ) *
    Real.sqrt e ^ m * Real.sqrt e ^ n * (1 - e) ^ l

lemma lcoefX_eq_bcoef_mul {η : ℝ} (hη1 : η ≤ 1) (m n ell : ℕ) :
    lcoefX η m n ell = bcoef η ell m * bcoef η ell n := by
  unfold lcoefX bcoef
  have h_sq : Real.sqrt (1 - η) ^ ell * Real.sqrt (1 - η) ^ ell = (1 - η) ^ ell := by
    rw [← mul_pow, Real.mul_self_sqrt (by linarith)]
  calc Real.sqrt ((m + ell).choose ell : ℝ) * Real.sqrt ((n + ell).choose ell : ℝ) *
        Real.sqrt η ^ m * Real.sqrt η ^ n * (1 - η) ^ ell
      = Real.sqrt ((m + ell).choose ell : ℝ) * Real.sqrt ((n + ell).choose ell : ℝ) *
        Real.sqrt η ^ m * Real.sqrt η ^ n * (Real.sqrt (1 - η) ^ ell * Real.sqrt (1 - η) ^ ell) := by
          rw [h_sq]
    _ = _ := by ring

lemma bs_pow_eq {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (β : ℂ) (ell m j r u v : ℕ)
    (hrj : r ≤ j) (hu_ell : u ≤ ell) (hv_m : v ≤ m) (hur : u ≤ r) (hvr : v ≤ j - r) :
    (((Real.sqrt (1 - η) : ℝ) : ℂ) * β) ^ (ell - u) *
      (-star (((Real.sqrt (1 - η) : ℝ) : ℂ) * β)) ^ (r - u) *
      ((((Real.sqrt η : ℝ) : ℂ) * β) ^ (m - v) *
        (-star (((Real.sqrt η : ℝ) : ℂ) * β)) ^ (j - r - v)) *
      (((Real.sqrt η ^ (j - r) * Real.sqrt (1 - η) ^ r : ℝ) : ℂ)) =
    (((Real.sqrt η ^ m * Real.sqrt (1 - η) ^ ell : ℝ) : ℂ) *
      β ^ (m + ell - (u + v)) * (-star β) ^ (j - (u + v))) *
      (((1 - η : ℝ) : ℂ) ^ (r - u) * (η : ℂ) ^ (j - v - r)) := by
  have h_s1 : (((Real.sqrt (1 - η) : ℝ) : ℂ)) * (((Real.sqrt (1 - η) : ℝ) : ℂ)) = ((1 - η : ℝ) : ℂ) := by
    exact_mod_cast Real.mul_self_sqrt (by linarith)
  have h_s2 : (((Real.sqrt η : ℝ) : ℂ)) * (((Real.sqrt η : ℝ) : ℂ)) = (η : ℂ) := by
    exact_mod_cast Real.mul_self_sqrt hη0
  have h_star1 : -star (((Real.sqrt (1 - η) : ℝ) : ℂ) * β) =
      (((Real.sqrt (1 - η) : ℝ) : ℂ)) * (-star β) := by
    simp only [star_mul', Complex.star_def, Complex.conj_ofReal]
    ring
  have h_star2 : -star (((Real.sqrt η : ℝ) : ℂ) * β) =
      (((Real.sqrt η : ℝ) : ℂ)) * (-star β) := by
    simp only [star_mul', Complex.star_def, Complex.conj_ofReal]
    ring
  have h_ell_eq : ell = (ell - u) + u := by omega
  have h_m_eq : m = (m - v) + v := by omega
  have h_r_eq : r = (r - u) + u := by omega
  have h_jr_eq : j - r = (j - v - r) + v := by omega
  have h_jrv_eq : j - r - v = j - v - r := by omega
  have h_mell_eq : m + ell - (u + v) = (ell - u) + (m - v) := by omega
  have h_juv_eq : j - (u + v) = (r - u) + (j - v - r) := by omega
  rw [h_star1, h_star2, h_jrv_eq, h_mell_eq, h_juv_eq]
  have h_p1 : (((Real.sqrt (1 - η) ^ ell : ℝ) : ℂ)) =
      (((Real.sqrt (1 - η) : ℝ) : ℂ)) ^ (ell - u) * (((Real.sqrt (1 - η) : ℝ) : ℂ)) ^ u := by
    push_cast
    rw [← pow_add, ← h_ell_eq]
  have h_p2 : (((Real.sqrt η ^ m : ℝ) : ℂ)) =
      (((Real.sqrt η : ℝ) : ℂ)) ^ (m - v) * (((Real.sqrt η : ℝ) : ℂ)) ^ v := by
    push_cast
    rw [← pow_add, ← h_m_eq]
  have h_p3 : (((Real.sqrt (1 - η) ^ r : ℝ) : ℂ)) =
      (((Real.sqrt (1 - η) : ℝ) : ℂ)) ^ (r - u) * (((Real.sqrt (1 - η) : ℝ) : ℂ)) ^ u := by
    push_cast
    rw [← pow_add, ← h_r_eq]
  have h_p4 : (((Real.sqrt η ^ (j - r) : ℝ) : ℂ)) =
      (((Real.sqrt η : ℝ) : ℂ)) ^ (j - v - r) * (((Real.sqrt η : ℝ) : ℂ)) ^ v := by
    push_cast
    rw [← pow_add, ← h_jr_eq]
  rw [Complex.ofReal_mul (Real.sqrt η ^ (j - r)), Complex.ofReal_mul (Real.sqrt η ^ m)]
  rw [h_p1, h_p2, h_p3, h_p4, ← h_s1, ← h_s2]
  simp only [pow_add, mul_pow]
  ring

lemma sum_range_min_le (a b N : ℕ) (hb : b ≤ N) (f : ℕ → ℂ) :
    (∑ u ∈ range (min a b + 1), f u) =
      ∑ u ∈ range (N + 1), if u ≤ a ∧ u ≤ b then f u else 0 := by
  rw [sum_range_min a b]
  have hN : N + 1 = (b + 1) + (N - b) := by omega
  conv_rhs => rw [hN, sum_range_add]
  have h2 : (∑ x ∈ range (N - b), if b + 1 + x ≤ a ∧ b + 1 + x ≤ b then f (b + 1 + x) else 0) = 0 := by
    apply sum_eq_zero
    intro x _
    rw [if_neg (by omega)]
  rw [h2, add_zero]
  apply sum_congr rfl
  intro u hu
  rw [mem_range] at hu
  have hub : u ≤ b := by omega
  simp [hub]

lemma bcoef_mul_disp_lhs_eq (η : ℝ) (β : ℂ) (ell m j : ℕ) :
    (bcoef η ell m : ℂ) * displacementMatrix β (m + ell) j =
      (((Real.exp (-Complex.normSq β / 2) *
        Real.sqrt ((ell.factorial : ℝ) * (m.factorial : ℝ) * (j.factorial : ℝ)) *
        Real.sqrt η ^ m * Real.sqrt (1 - η) ^ ell : ℝ) : ℂ)) *
        ∑ u ∈ range (j + 1), ∑ v ∈ range (j + 1),
          if u ≤ ell ∧ v ≤ m ∧ u + v ≤ j then
            β ^ (m + ell - (u + v)) * (-star β) ^ (j - (u + v)) /
              ((u.factorial : ℂ) * ((ell - u).factorial : ℂ) *
                (v.factorial : ℂ) * ((m - v).factorial : ℂ) * ((j - (u + v)).factorial : ℂ))
          else 0 := by
  dsimp only [bcoef, displacementMatrix]
  rw [sum_range_min (m + ell) j]
  have h_pref :
    (Real.sqrt ((m + ell).choose ell : ℝ) * Real.sqrt η ^ m * Real.sqrt (1 - η) ^ ell) *
      (Real.exp (-Complex.normSq β / 2) *
        Real.sqrt (((m + ell).factorial : ℝ) * (j.factorial : ℝ))) =
    (Real.exp (-Complex.normSq β / 2) *
      Real.sqrt ((ell.factorial : ℝ) * (m.factorial : ℝ) * (j.factorial : ℝ)) *
      Real.sqrt η ^ m * Real.sqrt (1 - η) ^ ell) *
      (((m + ell).factorial : ℝ) / ((ell.factorial : ℝ) * (m.factorial : ℝ))) := by
    have h_ch : ((m + ell).choose ell : ℝ) =
        ((m + ell).factorial : ℝ) / ((ell.factorial : ℝ) * (m.factorial : ℝ)) := by
      have h_f : ((m + ell).factorial : ℝ) =
          ((m + ell).choose ell : ℝ) * (m.factorial : ℝ) * (ell.factorial : ℝ) := by
        exact_mod_cast (Nat.add_choose_mul_factorial_mul_factorial m ell).symm
      have hm_ne : (m.factorial : ℝ) ≠ 0 := by exact_mod_cast m.factorial_ne_zero
      have hell_ne : (ell.factorial : ℝ) ≠ 0 := by exact_mod_cast ell.factorial_ne_zero
      rw [h_f]
      field_simp
    have h_sqrt_ch :
      Real.sqrt ((m + ell).choose ell : ℝ) *
        Real.sqrt (((m + ell).factorial : ℝ) * (j.factorial : ℝ)) =
      Real.sqrt ((ell.factorial : ℝ) * (m.factorial : ℝ) * (j.factorial : ℝ)) *
        (((m + ell).factorial : ℝ) / ((ell.factorial : ℝ) * (m.factorial : ℝ))) := by
      have hm_pos : (0 : ℝ) < m.factorial := by exact_mod_cast m.factorial_pos
      have hell_pos : (0 : ℝ) < ell.factorial := by exact_mod_cast ell.factorial_pos
      have h_em_pos : (0 : ℝ) < (ell.factorial : ℝ) * (m.factorial : ℝ) := mul_pos hell_pos hm_pos
      rw [h_ch, Real.sqrt_div (by positivity), Real.sqrt_mul (by positivity) (j.factorial : ℝ),
        Real.sqrt_mul h_em_pos.le (j.factorial : ℝ)]
      have h_sq_m : Real.sqrt ((m + ell).factorial : ℝ) * Real.sqrt ((m + ell).factorial : ℝ) =
          ((m + ell).factorial : ℝ) := Real.mul_self_sqrt (by positivity)
      have h_sq_em : Real.sqrt ((ell.factorial : ℝ) * (m.factorial : ℝ)) *
          Real.sqrt ((ell.factorial : ℝ) * (m.factorial : ℝ)) =
          (ell.factorial : ℝ) * (m.factorial : ℝ) := Real.mul_self_sqrt h_em_pos.le
      have h_em_s_ne : Real.sqrt ((ell.factorial : ℝ) * (m.factorial : ℝ)) ≠ 0 :=
        (Real.sqrt_pos.2 h_em_pos).ne'
      calc Real.sqrt (((m + ell).factorial : ℝ)) / Real.sqrt ((ell.factorial : ℝ) * (m.factorial : ℝ)) *
            (Real.sqrt (((m + ell).factorial : ℝ)) * Real.sqrt (j.factorial : ℝ))
          = (Real.sqrt (((m + ell).factorial : ℝ)) * Real.sqrt (((m + ell).factorial : ℝ))) *
            Real.sqrt (j.factorial : ℝ) / Real.sqrt ((ell.factorial : ℝ) * (m.factorial : ℝ)) := by ring
        _ = ((m + ell).factorial : ℝ) * Real.sqrt (j.factorial : ℝ) *
            Real.sqrt ((ell.factorial : ℝ) * (m.factorial : ℝ)) /
            (Real.sqrt ((ell.factorial : ℝ) * (m.factorial : ℝ)) *
             Real.sqrt ((ell.factorial : ℝ) * (m.factorial : ℝ))) := by
            rw [h_sq_m]
            field_simp
        _ = _ := by
            rw [h_sq_em]
            ring
    calc (Real.sqrt ((m + ell).choose ell : ℝ) * Real.sqrt η ^ m * Real.sqrt (1 - η) ^ ell) *
          (Real.exp (-Complex.normSq β / 2) *
            Real.sqrt (((m + ell).factorial : ℝ) * (j.factorial : ℝ)))
        = Real.exp (-Complex.normSq β / 2) * Real.sqrt η ^ m * Real.sqrt (1 - η) ^ ell *
          (Real.sqrt ((m + ell).choose ell : ℝ) *
            Real.sqrt (((m + ell).factorial : ℝ) * (j.factorial : ℝ))) := by ring
      _ = _ := by rw [h_sqrt_ch]; ring
  rw [← mul_assoc, ← Complex.ofReal_mul, h_pref, Complex.ofReal_mul, mul_assoc]
  congr 1
  rw [mul_sum]
  have h_p_sum : ∀ p ∈ range (j + 1),
      ((((m + ell).factorial : ℝ) / ((ell.factorial : ℝ) * (m.factorial : ℝ)) : ℝ) : ℂ) *
        (if p ≤ m + ell then
          β ^ (m + ell - p) * (-star β) ^ (j - p) /
            ((p.factorial : ℂ) * ((m + ell - p).factorial : ℂ) * ((j - p).factorial : ℂ))
        else 0) =
      ∑ u ∈ range (j + 1),
        if u ≤ p then
          if u ≤ ell ∧ p - u ≤ m ∧ u + (p - u) ≤ j then
            β ^ (m + ell - (u + (p - u))) * (-star β) ^ (j - (u + (p - u))) /
              ((u.factorial : ℂ) * ((ell - u).factorial : ℂ) *
                (((p - u).factorial : ℂ)) * ((m - (p - u)).factorial : ℂ) *
                (((j - (u + (p - u))).factorial : ℂ)))
          else 0
        else 0 := by
    intro p hp
    rw [mem_range] at hp
    have hpj : p ≤ j := by omega
    have h_lhs_p :
      ((((m + ell).factorial : ℝ) / ((ell.factorial : ℝ) * (m.factorial : ℝ)) : ℝ) : ℂ) *
        (if p ≤ m + ell then
          β ^ (m + ell - p) * (-star β) ^ (j - p) /
            ((p.factorial : ℂ) * ((m + ell - p).factorial : ℂ) * ((j - p).factorial : ℂ))
        else 0) =
      (if p ≤ m + ell ∧ ell ≤ m + ell then
        (((m + ell).factorial : ℂ) / ((p.factorial : ℂ) * ((m + ell - p).factorial : ℂ) *
          (ell.factorial : ℂ) * ((m + ell - ell).factorial : ℂ)))
      else 0) *
      (β ^ (m + ell - p) * (-star β) ^ (j - p) / ((j - p).factorial : ℂ)) := by
      have h_le_ell : ell ≤ m + ell := Nat.le_add_left ell m
      have h_sub_ell : m + ell - ell = m := Nat.add_sub_cancel m ell
      rw [h_sub_ell]
      by_cases hpm : p ≤ m + ell
      · simp only [hpm, h_le_ell, and_self, ↓reduceIte]
        push_cast
        ring
      · simp [hpm]
    rw [h_lhs_p, vandermonde_fact j (m + ell) p ell hpj, sum_mul]
    apply sum_congr rfl
    intro u _
    by_cases hup : u ≤ p
    · rw [if_pos hup]
      have h_add_sub : u + (p - u) = p := Nat.add_sub_of_le hup
      have h_cond : (u ≤ p ∧ u ≤ ell ∧ p + ell - u ≤ m + ell) ↔
          (u ≤ ell ∧ p - u ≤ m ∧ u + (p - u) ≤ j) := by omega
      by_cases hc : u ≤ ell ∧ p - u ≤ m ∧ u + (p - u) ≤ j
      · have hc' : u ≤ p ∧ u ≤ ell ∧ p + ell - u ≤ m + ell := h_cond.mpr hc
        rw [if_pos hc', if_pos hc, h_add_sub]
        have h_sub_m : m + ell - (p + ell - u) = m - (p - u) := by omega
        rw [h_sub_m]
        ring
      · have hc' : ¬ (u ≤ p ∧ u ≤ ell ∧ p + ell - u ≤ m + ell) := fun h => hc (h_cond.mp h)
        rw [if_neg hc', if_neg hc, zero_mul]
    · have hc' : ¬ (u ≤ p ∧ u ≤ ell ∧ p + ell - u ≤ m + ell) := by omega
      rw [if_neg hc', if_neg hup, zero_mul]
  rw [sum_congr rfl h_p_sum, sum_comm]
  apply sum_congr rfl
  intro u hu
  rw [mem_range] at hu
  have huj : u ≤ j := by omega
  let G : ℕ → ℂ := fun v =>
    if u ≤ ell ∧ v ≤ m ∧ u + v ≤ j then
      β ^ (m + ell - (u + v)) * (-star β) ^ (j - (u + v)) /
        ((u.factorial : ℂ) * ((ell - u).factorial : ℂ) *
          (v.factorial : ℂ) * ((m - v).factorial : ℂ) * ((j - (u + v)).factorial : ℂ))
    else 0
  have hG : (∑ p ∈ range (j + 1),
      if u ≤ p then
        if u ≤ ell ∧ p - u ≤ m ∧ u + (p - u) ≤ j then
          β ^ (m + ell - (u + (p - u))) * (-star β) ^ (j - (u + (p - u))) /
            ((u.factorial : ℂ) * ((ell - u).factorial : ℂ) *
              (((p - u).factorial : ℂ)) * ((m - (p - u)).factorial : ℂ) *
              (((j - (u + (p - u))).factorial : ℂ)))
        else 0
      else 0) = ∑ p ∈ range (j + 1), if u ≤ p then G (p - u) else 0 := rfl
  rw [hG, sum_range_sub_eq_sum_range_add j u huj G]
  apply sum_congr rfl
  intro v _
  dsimp only [G]
  by_cases huv : u + v ≤ j
  · rw [if_pos huv]
  · have hc : ¬ (u ≤ ell ∧ v ≤ m ∧ u + v ≤ j) := by omega
    rw [if_neg huv, if_neg hc]

lemma bcoef_mul_disp_eq {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (β : ℂ) (ell m j : ℕ) :
    (bcoef η ell m : ℂ) * displacementMatrix β (m + ell) j =
      ∑ r ∈ range (j + 1),
        displacementMatrix (((Real.sqrt (1 - η) : ℝ) : ℂ) * β) ell r *
        displacementMatrix (((Real.sqrt η : ℝ) : ℂ) * β) m (j - r) *
        (bcoef η r (j - r) : ℂ) := by
  rw [bcoef_mul_disp_lhs_eq η β ell m j]
  symm
  have h_rhs_r : ∀ r ∈ range (j + 1),
      displacementMatrix (((Real.sqrt (1 - η) : ℝ) : ℂ) * β) ell r *
        displacementMatrix (((Real.sqrt η : ℝ) : ℂ) * β) m (j - r) *
        (bcoef η r (j - r) : ℂ) =
      (((Real.exp (-Complex.normSq β / 2) *
        Real.sqrt ((ell.factorial : ℝ) * (m.factorial : ℝ) * (j.factorial : ℝ)) *
        Real.sqrt η ^ m * Real.sqrt (1 - η) ^ ell : ℝ) : ℂ)) *
        ∑ u ∈ range (j + 1), ∑ v ∈ range (j + 1),
          if u ≤ ell ∧ v ≤ m then
            if u ≤ r ∧ r ≤ j - v then
              (β ^ (m + ell - (u + v)) * (-star β) ^ (j - (u + v)) /
                ((u.factorial : ℂ) * ((ell - u).factorial : ℂ) *
                  (v.factorial : ℂ) * ((m - v).factorial : ℂ))) *
              (((1 - η : ℝ) : ℂ) ^ (r - u) * (η : ℂ) ^ (j - v - r) /
                (((r - u).factorial : ℂ) * ((j - v - r).factorial : ℂ)))
            else 0
          else 0 := by
    intro r hr
    rw [mem_range] at hr
    have hrj : r ≤ j := by omega
    have hjr : j - r ≤ j := Nat.sub_le j r
    dsimp only [displacementMatrix, bcoef]
    rw [sum_range_min_le ell r j hrj, sum_range_min_le m (j - r) j hjr]
    have h_pref_r :
      (Real.exp (-Complex.normSq (((Real.sqrt (1 - η) : ℝ) : ℂ) * β) / 2) *
        Real.sqrt ((ell.factorial : ℝ) * (r.factorial : ℝ))) *
      (Real.exp (-Complex.normSq (((Real.sqrt η : ℝ) : ℂ) * β) / 2) *
        Real.sqrt ((m.factorial : ℝ) * ((j - r).factorial : ℝ))) *
      Real.sqrt ((j - r + r).choose r : ℝ) =
      Real.exp (-Complex.normSq β / 2) *
        Real.sqrt ((ell.factorial : ℝ) * (m.factorial : ℝ) * (j.factorial : ℝ)) := by
      have h_ns1 : Complex.normSq (((Real.sqrt (1 - η) : ℝ) : ℂ) * β) = (1 - η) * Complex.normSq β := by
        rw [Complex.normSq_mul, Complex.normSq_ofReal, Real.mul_self_sqrt (by linarith)]
      have h_ns2 : Complex.normSq (((Real.sqrt η : ℝ) : ℂ) * β) = η * Complex.normSq β := by
        rw [Complex.normSq_mul, Complex.normSq_ofReal, Real.mul_self_sqrt hη0]
      have h_exp : Real.exp (-((1 - η) * Complex.normSq β) / 2) * Real.exp (-(η * Complex.normSq β) / 2) =
          Real.exp (-Complex.normSq β / 2) := by
        rw [← Real.exp_add]
        congr 1
        ring
      have h_jrr : j - r + r = j := Nat.sub_add_cancel hrj
      have h_jf : (j.factorial : ℝ) = (j.choose r : ℝ) * (r.factorial : ℝ) * ((j - r).factorial : ℝ) := by
        exact_mod_cast (Nat.choose_mul_factorial_mul_factorial hrj).symm
      have h_sqrt : Real.sqrt ((ell.factorial : ℝ) * (r.factorial : ℝ)) *
          Real.sqrt ((m.factorial : ℝ) * ((j - r).factorial : ℝ)) *
          Real.sqrt (j.choose r : ℝ) =
          Real.sqrt ((ell.factorial : ℝ) * (m.factorial : ℝ) * (j.factorial : ℝ)) := by
        rw [← Real.sqrt_mul (by positivity), ← Real.sqrt_mul (by positivity)]
        congr 1
        rw [h_jf]
        ring
      rw [h_ns1, h_ns2, h_jrr]
      calc (Real.exp (-((1 - η) * Complex.normSq β) / 2) *
            Real.sqrt ((ell.factorial : ℝ) * (r.factorial : ℝ))) *
           (Real.exp (-(η * Complex.normSq β) / 2) *
            Real.sqrt ((m.factorial : ℝ) * ((j - r).factorial : ℝ))) *
           Real.sqrt (j.choose r : ℝ)
          = (Real.exp (-((1 - η) * Complex.normSq β) / 2) *
             Real.exp (-(η * Complex.normSq β) / 2)) *
            (Real.sqrt ((ell.factorial : ℝ) * (r.factorial : ℝ)) *
             Real.sqrt ((m.factorial : ℝ) * ((j - r).factorial : ℝ)) *
             Real.sqrt (j.choose r : ℝ)) := by ring
        _ = _ := by rw [h_exp, h_sqrt]
    have h_rearr : ∀ (P1 P2 S1 S2 B1 B2 : ℂ),
        (P1 * S1) * (P2 * S2) * (B1 * B2) = (P1 * P2 * B1) * (S1 * S2 * B2) := by
      intros; ring
    have h_b_split :
      ((Real.sqrt ((j - r + r).choose r : ℝ) * Real.sqrt η ^ (j - r) * Real.sqrt (1 - η) ^ r : ℝ) : ℂ) =
      ((Real.sqrt ((j - r + r).choose r : ℝ) : ℝ) : ℂ) *
        ((Real.sqrt η ^ (j - r) * Real.sqrt (1 - η) ^ r : ℝ) : ℂ) := by
      push_cast; ring
    have h_pref_r_c :
      (((Real.exp (-Complex.normSq (((Real.sqrt (1 - η) : ℝ) : ℂ) * β) / 2) *
        Real.sqrt ((ell.factorial : ℝ) * (r.factorial : ℝ)) : ℝ) : ℂ) *
       ((Real.exp (-Complex.normSq (((Real.sqrt η : ℝ) : ℂ) * β) / 2) *
        Real.sqrt ((m.factorial : ℝ) * ((j - r).factorial : ℝ)) : ℝ) : ℂ) *
       ((Real.sqrt ((j - r + r).choose r : ℝ) : ℝ) : ℂ)) =
      (((Real.exp (-Complex.normSq β / 2) *
        Real.sqrt ((ell.factorial : ℝ) * (m.factorial : ℝ) * (j.factorial : ℝ)) : ℝ) : ℂ)) := by
      exact_mod_cast h_pref_r
    have h_pref_split :
      (((Real.exp (-Complex.normSq β / 2) *
        Real.sqrt ((ell.factorial : ℝ) * (m.factorial : ℝ) * (j.factorial : ℝ)) *
        Real.sqrt η ^ m * Real.sqrt (1 - η) ^ ell : ℝ) : ℂ)) =
      (((Real.exp (-Complex.normSq β / 2) *
        Real.sqrt ((ell.factorial : ℝ) * (m.factorial : ℝ) * (j.factorial : ℝ)) : ℝ) : ℂ)) *
      (((Real.sqrt η ^ m * Real.sqrt (1 - η) ^ ell : ℝ) : ℂ)) := by
      rw [mul_assoc (Real.exp _ * _), Complex.ofReal_mul]
    rw [h_b_split, h_rearr, h_pref_r_c, h_pref_split,
      mul_assoc (((Real.exp (-Complex.normSq β / 2) *
        Real.sqrt ((ell.factorial : ℝ) * (m.factorial : ℝ) * (j.factorial : ℝ)) : ℝ) : ℂ))]
    congr 1
    rw [sum_mul_sum, sum_mul, mul_sum]
    apply sum_congr rfl
    intro u _
    rw [sum_mul, mul_sum]
    apply sum_congr rfl
    intro v hv
    rw [mem_range] at hv
    by_cases huv_em : u ≤ ell ∧ v ≤ m
    · rw [if_pos huv_em]
      by_cases hur : u ≤ r ∧ r ≤ j - v
      · have hvr : v ≤ j - r := by omega
        have h1 : u ≤ ell ∧ u ≤ r := ⟨huv_em.1, hur.1⟩
        have h2 : v ≤ m ∧ v ≤ j - r := ⟨huv_em.2, hvr⟩
        rw [if_pos h1, if_pos h2, if_pos hur]
        have h_pow := bs_pow_eq hη0 hη1 β ell m j r u v hrj huv_em.1 huv_em.2 hur.1 hvr
        have h_sub_jrv : j - r - v = j - v - r := by omega
        rw [h_sub_jrv] at h_pow ⊢
        linear_combination
          (1 / ((u.factorial : ℂ) * ((ell - u).factorial : ℂ) * ((r - u).factorial : ℂ) *
            (v.factorial : ℂ) * ((m - v).factorial : ℂ) * ((j - v - r).factorial : ℂ))) * h_pow
      · have h_zero :
          (if u ≤ ell ∧ u ≤ r then
            (((Real.sqrt (1 - η) : ℝ) : ℂ) * β) ^ (ell - u) *
              (-star (((Real.sqrt (1 - η) : ℝ) : ℂ) * β)) ^ (r - u) /
              ((u.factorial : ℂ) * ((ell - u).factorial : ℂ) * ((r - u).factorial : ℂ))
          else 0) *
          (if v ≤ m ∧ v ≤ j - r then
            (((Real.sqrt η : ℝ) : ℂ) * β) ^ (m - v) *
              (-star (((Real.sqrt η : ℝ) : ℂ) * β)) ^ (j - r - v) /
              ((v.factorial : ℂ) * ((m - v).factorial : ℂ) * ((j - r - v).factorial : ℂ))
          else 0) = 0 := by
          by_cases h1 : u ≤ r
          · have h2 : ¬ (v ≤ m ∧ v ≤ j - r) := by omega
            rw [if_neg h2, mul_zero]
          · have h1' : ¬ (u ≤ ell ∧ u ≤ r) := by omega
            rw [if_neg h1', zero_mul]
        rw [if_neg hur, h_zero, zero_mul, mul_zero]
    · rw [if_neg huv_em, mul_zero]
      by_cases h1 : u ≤ ell
      · have h2 : ¬ (v ≤ m ∧ v ≤ j - r) := by omega
        rw [if_neg h2, mul_zero, zero_mul]
      · have h1' : ¬ (u ≤ ell ∧ u ≤ r) := by omega
        rw [if_neg h1', zero_mul, zero_mul]
  rw [sum_congr rfl h_rhs_r, ← mul_sum]
  congr 1
  have h_swap :
    (∑ r ∈ range (j + 1), ∑ u ∈ range (j + 1), ∑ v ∈ range (j + 1),
      if u ≤ ell ∧ v ≤ m then
        if u ≤ r ∧ r ≤ j - v then
          (β ^ (m + ell - (u + v)) * (-star β) ^ (j - (u + v)) /
            ((u.factorial : ℂ) * ((ell - u).factorial : ℂ) *
              (v.factorial : ℂ) * ((m - v).factorial : ℂ))) *
          (((1 - η : ℝ) : ℂ) ^ (r - u) * (η : ℂ) ^ (j - v - r) /
            (((r - u).factorial : ℂ) * ((j - v - r).factorial : ℂ)))
        else 0
      else 0) =
    ∑ u ∈ range (j + 1), ∑ v ∈ range (j + 1), ∑ r ∈ range (j + 1),
      if u ≤ ell ∧ v ≤ m then
        if u ≤ r ∧ r ≤ j - v then
          (β ^ (m + ell - (u + v)) * (-star β) ^ (j - (u + v)) /
            ((u.factorial : ℂ) * ((ell - u).factorial : ℂ) *
              (v.factorial : ℂ) * ((m - v).factorial : ℂ))) *
          (((1 - η : ℝ) : ℂ) ^ (r - u) * (η : ℂ) ^ (j - v - r) /
            (((r - u).factorial : ℂ) * ((j - v - r).factorial : ℂ)))
        else 0
      else 0 := by
    rw [sum_comm]
    apply sum_congr rfl
    intro u _
    rw [sum_comm]
  rw [h_swap]
  apply sum_congr rfl
  intro u hu
  rw [mem_range] at hu
  apply sum_congr rfl
  intro v hv
  rw [mem_range] at hv
  by_cases huv_em : u ≤ ell ∧ v ≤ m
  · by_cases huv_j : u + v ≤ j
    · have h_all : u ≤ ell ∧ v ≤ m ∧ u + v ≤ j := ⟨huv_em.1, huv_em.2, huv_j⟩
      rw [if_pos h_all]
      let fr : ℕ → ℂ := fun s =>
        (β ^ (m + ell - (u + v)) * (-star β) ^ (j - (u + v)) /
          ((u.factorial : ℂ) * ((ell - u).factorial : ℂ) *
            (v.factorial : ℂ) * ((m - v).factorial : ℂ))) *
        (((1 - η : ℝ) : ℂ) ^ s * (η : ℂ) ^ ((j - (u + v)) - s) /
          ((s.factorial : ℂ) * (((j - (u + v)) - s).factorial : ℂ)))
      have h_r_eq :
        (∑ r ∈ range (j + 1),
          if u ≤ ell ∧ v ≤ m then
            if u ≤ r ∧ r ≤ j - v then
              (β ^ (m + ell - (u + v)) * (-star β) ^ (j - (u + v)) /
                ((u.factorial : ℂ) * ((ell - u).factorial : ℂ) *
                  (v.factorial : ℂ) * ((m - v).factorial : ℂ))) *
              (((1 - η : ℝ) : ℂ) ^ (r - u) * (η : ℂ) ^ (j - v - r) /
                (((r - u).factorial : ℂ) * ((j - v - r).factorial : ℂ)))
            else 0
          else 0) =
        ∑ r ∈ range (j + 1), if u ≤ r ∧ r ≤ j - v then fr (r - u) else 0 := by
        apply sum_congr rfl
        intro r _
        rw [if_pos huv_em]
        split_ifs with hur
        · dsimp only [fr]
          have : j - v - r = (j - (u + v)) - (r - u) := by omega
          rw [this]
        · rfl
      have hujv : u ≤ j - v := by omega
      have hjvj : j - v ≤ j := Nat.sub_le j v
      rw [h_r_eq, sum_range_ite_interval j u (j - v) hujv hjvj fr]
      dsimp only [fr]
      have h_sub_jv : j - v - u = j - (u + v) := by omega
      rw [h_sub_jv, ← mul_sum, sum_bin_div_fact (j - (u + v)) ((1 - η : ℝ) : ℂ) (η : ℂ)]
      have h_add_one : ((1 - η : ℝ) : ℂ) + (η : ℂ) = 1 := by push_cast; ring
      rw [h_add_one, one_pow]
      ring
    · have h_not : ¬ (u ≤ ell ∧ v ≤ m ∧ u + v ≤ j) := by omega
      rw [if_neg h_not]
      apply sum_eq_zero
      intro r _
      rw [if_pos huv_em, if_neg (by omega)]
  · have h_not : ¬ (u ≤ ell ∧ v ≤ m ∧ u + v ≤ j) := by omega
    rw [if_neg h_not]
    apply sum_eq_zero
    intro r _
    rw [if_neg huv_em]

lemma hasSum_loss_disp_entry {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (β : ℂ) (m n j k : ℕ) :
    HasSum (fun ell : ℕ =>
      (lcoefX η m n ell : ℂ) * displacementMatrix β (m + ell) j * star (displacementMatrix β (n + ell) k))
      (∑ r ∈ range (min j k + 1),
        displacementMatrix (((Real.sqrt η : ℝ) : ℂ) * β) m (j - r) *
        (lcoefX η (j - r) (k - r) r : ℂ) *
        star (displacementMatrix (((Real.sqrt η : ℝ) : ℂ) * β) n (k - r))) := by
  let z1 : ℂ := ((Real.sqrt (1 - η) : ℝ) : ℂ) * β
  let z2 : ℂ := ((Real.sqrt η : ℝ) : ℂ) * β
  let C_rr : ℕ → ℕ → ℂ := fun r r' =>
    displacementMatrix z2 m (j - r) * (bcoef η r (j - r) : ℂ) *
      star (displacementMatrix z2 n (k - r')) * (bcoef η r' (k - r') : ℂ)
  have h_summand : ∀ ell : ℕ,
      (lcoefX η m n ell : ℂ) * displacementMatrix β (m + ell) j * star (displacementMatrix β (n + ell) k) =
      ∑ r ∈ range (j + 1), ∑ r' ∈ range (k + 1),
        C_rr r r' * (displacementMatrix z1 ell r * star (displacementMatrix z1 ell r')) := by
    intro ell
    rw [lcoefX_eq_bcoef_mul hη1 m n ell, Complex.ofReal_mul]
    have h_rearr :
      ((bcoef η ell m : ℂ) * (bcoef η ell n : ℂ)) *
        displacementMatrix β (m + ell) j * star (displacementMatrix β (n + ell) k) =
      ((bcoef η ell m : ℂ) * displacementMatrix β (m + ell) j) *
        star ((bcoef η ell n : ℂ) * displacementMatrix β (n + ell) k) := by
      simp only [star_mul', Complex.star_def, Complex.conj_ofReal]
      ring
    rw [h_rearr, bcoef_mul_disp_eq hη0 hη1 β ell m j, bcoef_mul_disp_eq hη0 hη1 β ell n k]
    rw [star_sum, sum_mul_sum]
    apply sum_congr rfl
    intro r _
    apply sum_congr rfl
    intro r' _
    dsimp only [C_rr, z1, z2]
    simp only [star_mul', Complex.star_def, Complex.conj_ofReal]
    ring
  rw [funext h_summand]
  have h_sum2 : HasSum (fun ell : ℕ =>
      ∑ r ∈ range (j + 1), ∑ r' ∈ range (k + 1),
        C_rr r r' * (displacementMatrix z1 ell r * star (displacementMatrix z1 ell r')))
      (∑ r ∈ range (j + 1), ∑ r' ∈ range (k + 1),
        C_rr r r' * (if r = r' then 1 else 0)) :=
    hasSum_sum (fun r _ => hasSum_sum (fun r' _ =>
      (hasSum_disp_col_ortho z1 r r').mul_left (C_rr r r')))
  suffices h_eq :
    (∑ r ∈ range (j + 1), ∑ r' ∈ range (k + 1),
      C_rr r r' * (if r = r' then 1 else 0)) =
    ∑ r ∈ range (min j k + 1),
      displacementMatrix z2 m (j - r) *
      (lcoefX η (j - r) (k - r) r : ℂ) *
      star (displacementMatrix z2 n (k - r)) by
    rwa [h_eq] at h_sum2
  rw [min_comm j k, sum_range_min k j]
  apply sum_congr rfl
  intro r _
  have h_inner :
    (∑ r' ∈ range (k + 1), C_rr r r' * (if r = r' then 1 else 0)) =
    ∑ r' ∈ range (k + 1), if r = r' then C_rr r r' else 0 := by
    apply sum_congr rfl
    intro r' _
    split_ifs <;> ring
  rw [h_inner, sum_ite_eq]
  have h_lt : (r < k + 1) ↔ (r ≤ k) := by omega
  simp only [mem_range, h_lt]
  split_ifs with hrk
  · dsimp only [C_rr]
    rw [lcoefX_eq_bcoef_mul hη1 (j - r) (k - r) r, Complex.ofReal_mul]
    ring
  · rfl

lemma sqrt_fact_div_eq (n j : ℕ) (hj : j ≤ n) :
    Real.sqrt (n.factorial : ℝ) / (Real.sqrt (j.factorial : ℝ) * ((n - j).factorial : ℝ)) =
      Real.sqrt (n.choose j : ℝ) / Real.sqrt ((n - j).factorial : ℝ) := by
  have h_nf : (n.factorial : ℝ) = (n.choose j : ℝ) * (j.factorial : ℝ) * ((n - j).factorial : ℝ) := by
    exact_mod_cast (Nat.choose_mul_factorial_mul_factorial hj).symm
  have hj_pos : (0 : ℝ) < (j.factorial : ℝ) := Nat.cast_pos.2 j.factorial_pos
  have hnj_pos : (0 : ℝ) < ((n - j).factorial : ℝ) := Nat.cast_pos.2 (n - j).factorial_pos
  have h_sq_nj : Real.sqrt ((n - j).factorial : ℝ) * Real.sqrt ((n - j).factorial : ℝ) =
      ((n - j).factorial : ℝ) := Real.mul_self_sqrt hnj_pos.le
  rw [h_nf, Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity)]
  conv_lhs => rhs; rw [← h_sq_nj]
  have hj_s_ne : Real.sqrt (j.factorial : ℝ) ≠ 0 := (Real.sqrt_pos.2 hj_pos).ne'
  have hnj_s_ne : Real.sqrt ((n - j).factorial : ℝ) ≠ 0 := (Real.sqrt_pos.2 hnj_pos).ne'
  field_simp

lemma sqrt_mul_fact_div_eq (m n j : ℕ) (hjm : j ≤ m) (hjn : j ≤ n) :
    Real.sqrt ((m.factorial : ℝ) * (n.factorial : ℝ)) /
      ((j.factorial : ℝ) * ((m - j).factorial : ℝ) * ((n - j).factorial : ℝ)) =
    (Real.sqrt (m.choose j : ℝ) / Real.sqrt ((m - j).factorial : ℝ)) *
      (Real.sqrt (n.choose j : ℝ) / Real.sqrt ((n - j).factorial : ℝ)) := by
  have hj_pos : (0 : ℝ) < (j.factorial : ℝ) := Nat.cast_pos.2 j.factorial_pos
  have h_sq_j : (j.factorial : ℝ) = Real.sqrt (j.factorial : ℝ) * Real.sqrt (j.factorial : ℝ) :=
    (Real.mul_self_sqrt hj_pos.le).symm
  rw [Real.sqrt_mul (by positivity), h_sq_j]
  calc (Real.sqrt (m.factorial : ℝ) * Real.sqrt (n.factorial : ℝ)) /
        (Real.sqrt (j.factorial : ℝ) * Real.sqrt (j.factorial : ℝ) *
          ((m - j).factorial : ℝ) * ((n - j).factorial : ℝ))
      = (Real.sqrt (m.factorial : ℝ) / (Real.sqrt (j.factorial : ℝ) * ((m - j).factorial : ℝ))) *
        (Real.sqrt (n.factorial : ℝ) / (Real.sqrt (j.factorial : ℝ) * ((n - j).factorial : ℝ))) := by ring
    _ = _ := by rw [sqrt_fact_div_eq m j hjm, sqrt_fact_div_eq n j hjn]

noncomputable def dispFactor (z : ℂ) (n j : ℕ) : ℝ :=
  Real.sqrt (n.choose j : ℝ) * ‖z‖ ^ (n - j) / Real.sqrt ((n - j).factorial : ℝ)

lemma dispFactor_nonneg (z : ℂ) (n j : ℕ) : 0 ≤ dispFactor z n j := by
  unfold dispFactor; positivity

lemma norm_disp_le_sum_dispFactor (z : ℂ) (m n : ℕ) :
    ‖displacementMatrix z m n‖ ≤
      ∑ j ∈ range (min m n + 1), dispFactor z m j * dispFactor z n j := by
  unfold displacementMatrix
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have h_exp_le : Real.exp (-Complex.normSq z / 2) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    linarith [Complex.normSq_nonneg z]
  have h_pref_le : Real.exp (-Complex.normSq z / 2) * Real.sqrt ((m.factorial : ℝ) * (n.factorial : ℝ)) ≤
      1 * Real.sqrt ((m.factorial : ℝ) * (n.factorial : ℝ)) :=
    mul_le_mul_of_nonneg_right h_exp_le (by positivity)
  rw [one_mul] at h_pref_le
  refine le_trans (mul_le_mul_of_nonneg_right h_pref_le (norm_nonneg _)) ?_
  refine le_trans (mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)) ?_
  rw [mul_sum]
  apply sum_le_sum
  intro j hj
  rw [mem_range] at hj
  have hjm : j ≤ m := by omega
  have hjn : j ≤ n := by omega
  rw [norm_div, norm_mul, norm_pow, norm_pow, norm_neg, norm_star, norm_mul, norm_mul,
    Complex.norm_natCast, Complex.norm_natCast, Complex.norm_natCast]
  dsimp only [dispFactor]
  have h_eq := sqrt_mul_fact_div_eq m n j hjm hjn
  exact le_of_eq (calc Real.sqrt ((m.factorial : ℝ) * (n.factorial : ℝ)) *
        (‖z‖ ^ (m - j) * ‖z‖ ^ (n - j) /
          ((j.factorial : ℝ) * ((m - j).factorial : ℝ) * ((n - j).factorial : ℝ)))
      = (Real.sqrt ((m.factorial : ℝ) * (n.factorial : ℝ)) /
          ((j.factorial : ℝ) * ((m - j).factorial : ℝ) * ((n - j).factorial : ℝ))) *
        (‖z‖ ^ (m - j) * ‖z‖ ^ (n - j)) := by ring
    _ = (Real.sqrt (m.choose j : ℝ) * ‖z‖ ^ (m - j) / Real.sqrt ((m - j).factorial : ℝ)) *
        (Real.sqrt (n.choose j : ℝ) * ‖z‖ ^ (n - j) / Real.sqrt ((n - j).factorial : ℝ)) := by
        rw [h_eq]; ring)

lemma sqrt_natCast_le (N : ℕ) : Real.sqrt (N : ℝ) ≤ (N : ℝ) := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  · have h1 : (1 : ℝ) ≤ (N : ℝ) := Nat.one_le_cast.2 hN
    exact Real.sqrt_le_iff.2 ⟨by positivity, by nlinarith⟩

lemma sqrt_choose_le_pow {δ : ℝ} (hδ : 0 < δ) (n j : ℕ) (hj : j ≤ n) :
    Real.sqrt (n.choose j : ℝ) ≤ (1 + δ) ^ j * ((1 + δ) / δ) ^ (n - j) := by
  refine le_trans (sqrt_natCast_le (n.choose j)) ?_
  have hj_mem : j ∈ range (n + 1) := mem_range.2 (by omega)
  have h_sum : (1 : ℝ) ^ j * δ ^ (n - j) * (n.choose j : ℝ) ≤ (1 + δ) ^ n := by
    rw [add_pow]
    exact single_le_sum (f := fun k => (1 : ℝ) ^ k * δ ^ (n - k) * (n.choose k : ℝ))
      (fun k _ => by positivity) hj_mem
  have h_pow_split : (1 + δ) ^ n = (1 + δ) ^ j * (1 + δ) ^ (n - j) := by
    rw [← pow_add, Nat.add_sub_of_le hj]
  rw [one_pow, one_mul, h_pow_split] at h_sum
  rw [div_pow, ← mul_div_assoc, le_div_iff₀ (pow_pos hδ (n - j))]
  linarith

lemma pow_div_sqrt_fact_le (R : ℝ) (hR : 0 ≤ R) (k : ℕ) :
    R ^ k / Real.sqrt (k.factorial : ℝ) ≤ Real.exp (R ^ 2 / 2) := by
  have h_term : (R ^ 2) ^ k / (k.factorial : ℝ) ≤ Real.exp (R ^ 2) :=
    le_hasSum (rexp_hasSum (R ^ 2)) k (fun m _ => by positivity)
  have h_lhs : (R ^ 2) ^ k / (k.factorial : ℝ) = (R ^ k / Real.sqrt (k.factorial : ℝ)) ^ 2 := by
    rw [div_pow, Real.sq_sqrt (by positivity), ← pow_mul, mul_comm 2 k, pow_mul]
  have h_rhs : Real.exp (R ^ 2) = (Real.exp (R ^ 2 / 2)) ^ 2 := by
    conv_rhs => rw [sq, ← Real.exp_add]
    ring_nf
  rw [h_lhs, h_rhs] at h_term
  have h_sqrt := Real.sqrt_le_sqrt h_term
  rwa [Real.sqrt_sq (by positivity), Real.sqrt_sq (Real.exp_pos _).le] at h_sqrt

noncomputable def dispConst (z : ℂ) (δ : ℝ) : ℝ :=
  Real.exp ((2 * ((1 + δ) / δ) * ‖z‖) ^ 2 / 2)

lemma dispConst_pos (z : ℂ) (δ : ℝ) : 0 < dispConst z δ := by
  unfold dispConst; positivity

lemma dispFactor_le {δ : ℝ} (hδ : 0 < δ) (z : ℂ) (n j : ℕ) (hj : j ≤ n) :
    dispFactor z n j ≤ dispConst z δ * (1 + δ) ^ j * (1 / 2 : ℝ) ^ (n - j) := by
  dsimp only [dispFactor, dispConst]
  have h_ch := sqrt_choose_le_pow hδ n j hj
  have h_f := pow_div_sqrt_fact_le (2 * ((1 + δ) / δ) * ‖z‖) (by positivity) (n - j)
  have h_f2 : (((1 + δ) / δ) * ‖z‖) ^ (n - j) / Real.sqrt ((n - j).factorial : ℝ) ≤
      Real.exp ((2 * ((1 + δ) / δ) * ‖z‖) ^ 2 / 2) * (1 / 2 : ℝ) ^ (n - j) := by
    have h_split : (2 * ((1 + δ) / δ) * ‖z‖) ^ (n - j) / Real.sqrt ((n - j).factorial : ℝ) =
        2 ^ (n - j) * ((((1 + δ) / δ) * ‖z‖) ^ (n - j) / Real.sqrt ((n - j).factorial : ℝ)) := by
      rw [mul_assoc 2, mul_pow, mul_div_assoc]
    rw [h_split] at h_f
    have h_two : (1 / 2 : ℝ) ^ (n - j) * (2 : ℝ) ^ (n - j) = 1 := by
      rw [← mul_pow]
      norm_num
    calc (((1 + δ) / δ) * ‖z‖) ^ (n - j) / Real.sqrt ((n - j).factorial : ℝ)
        = ((1 / 2 : ℝ) ^ (n - j) * (2 : ℝ) ^ (n - j)) *
            ((((1 + δ) / δ) * ‖z‖) ^ (n - j) / Real.sqrt ((n - j).factorial : ℝ)) := by
          rw [h_two, one_mul]
      _ = (1 / 2 : ℝ) ^ (n - j) *
            (2 ^ (n - j) * ((((1 + δ) / δ) * ‖z‖) ^ (n - j) / Real.sqrt ((n - j).factorial : ℝ))) := by
          ring
      _ ≤ (1 / 2 : ℝ) ^ (n - j) * Real.exp ((2 * ((1 + δ) / δ) * ‖z‖) ^ 2 / 2) :=
          mul_le_mul_of_nonneg_left h_f (by positivity)
      _ = Real.exp ((2 * ((1 + δ) / δ) * ‖z‖) ^ 2 / 2) * (1 / 2 : ℝ) ^ (n - j) := by ring
  calc Real.sqrt (n.choose j : ℝ) * ‖z‖ ^ (n - j) / Real.sqrt ((n - j).factorial : ℝ)
      ≤ ((1 + δ) ^ j * ((1 + δ) / δ) ^ (n - j)) * ‖z‖ ^ (n - j) /
          Real.sqrt ((n - j).factorial : ℝ) := by
        gcongr
    _ = (1 + δ) ^ j * ((((1 + δ) / δ) * ‖z‖) ^ (n - j) / Real.sqrt ((n - j).factorial : ℝ)) := by
        rw [mul_pow]; ring
    _ ≤ (1 + δ) ^ j * (Real.exp ((2 * ((1 + δ) / δ) * ‖z‖) ^ 2 / 2) * (1 / 2 : ℝ) ^ (n - j)) :=
        mul_le_mul_of_nonneg_left h_f2 (by positivity)
    _ = Real.exp ((2 * ((1 + δ) / δ) * ‖z‖) ^ 2 / 2) * (1 + δ) ^ j * (1 / 2 : ℝ) ^ (n - j) := by
        ring

noncomputable def dispUpper (z : ℂ) (δ : ℝ) (m n : ℕ) : ℝ :=
  ∑ j ∈ range (m + 1),
    if j ≤ n then
      dispConst z δ ^ 2 * ((1 + δ) ^ 2) ^ m * (1 / 2 : ℝ) ^ (m - j) * (1 / 2 : ℝ) ^ (n - j)
    else 0

lemma norm_disp_le_dispUpper {δ : ℝ} (hδ : 0 < δ) (z : ℂ) (m n : ℕ) :
    ‖displacementMatrix z m n‖ ≤ dispUpper z δ m n := by
  refine le_trans (norm_disp_le_sum_dispFactor z m n) ?_
  rw [min_comm m n, sum_range_min n m]
  dsimp only [dispUpper]
  apply sum_le_sum
  intro j hj
  rw [mem_range] at hj
  have hjm : j ≤ m := by omega
  split_ifs with hjn
  · have h_pow_j : (1 + δ) ^ j ≤ (1 + δ) ^ m := pow_le_pow_right₀ (by linarith) hjm
    have hc_pos : 0 ≤ dispConst z δ := (dispConst_pos z δ).le
    have h1 : dispFactor z m j ≤ dispConst z δ * (1 + δ) ^ m * (1 / 2 : ℝ) ^ (m - j) := by
      refine le_trans (dispFactor_le hδ z m j hjm) ?_
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h_pow_j hc_pos) (by positivity)
    have h2 : dispFactor z n j ≤ dispConst z δ * (1 + δ) ^ m * (1 / 2 : ℝ) ^ (n - j) := by
      refine le_trans (dispFactor_le hδ z n j hjn) ?_
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h_pow_j hc_pos) (by positivity)
    calc dispFactor z m j * dispFactor z n j
        ≤ (dispConst z δ * (1 + δ) ^ m * (1 / 2 : ℝ) ^ (m - j)) *
            (dispConst z δ * (1 + δ) ^ m * (1 / 2 : ℝ) ^ (n - j)) :=
          mul_le_mul h1 h2 (dispFactor_nonneg z n j) (by positivity)
      _ = dispConst z δ ^ 2 * ((1 + δ) ^ 2) ^ m * (1 / 2 : ℝ) ^ (m - j) * (1 / 2 : ℝ) ^ (n - j) := by
          rw [sq (1 + δ), mul_pow]; ring
  · rfl

lemma hasSum_dispUpper (δ : ℝ) (z : ℂ) (m : ℕ) :
    HasSum (fun n : ℕ => dispUpper z δ m n)
      (∑ j ∈ range (m + 1),
        dispConst z δ ^ 2 * ((1 + δ) ^ 2) ^ m * (1 / 2 : ℝ) ^ (m - j) * 2) :=
  hasSum_sum (fun j _ =>
    hasSum_ite_le_real j
      (fun d => dispConst z δ ^ 2 * ((1 + δ) ^ 2) ^ m * (1 / 2 : ℝ) ^ (m - j) * (1 / 2 : ℝ) ^ d)
      (hasSum_geometric_two.mul_left _))

lemma sum_half_pow_sub_le (m : ℕ) :
    (∑ j ∈ range (m + 1), (1 / 2 : ℝ) ^ (m - j)) ≤ 2 := by
  have h_ref := sum_range_reflect (fun j => (1 / 2 : ℝ) ^ j) (m + 1)
  simp only [Nat.add_sub_cancel] at h_ref
  rw [h_ref]
  exact sum_le_hasSum (range (m + 1)) (fun k _ => by positivity) hasSum_geometric_two

lemma summable_norm_disp (z : ℂ) (m : ℕ) :
    Summable (fun n : ℕ => ‖displacementMatrix z m n‖) :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (norm_disp_le_dispUpper zero_lt_one z m)
    (hasSum_dispUpper 1 z m).summable

lemma tsum_norm_disp_le {δ : ℝ} (hδ : 0 < δ) (z : ℂ) (m : ℕ) :
    (∑' n : ℕ, ‖displacementMatrix z m n‖) ≤ 4 * dispConst z δ ^ 2 * ((1 + δ) ^ 2) ^ m := by
  have h_le : (∑' n : ℕ, ‖displacementMatrix z m n‖) ≤
      ∑ j ∈ range (m + 1), dispConst z δ ^ 2 * ((1 + δ) ^ 2) ^ m * (1 / 2 : ℝ) ^ (m - j) * 2 :=
    hasSum_le (norm_disp_le_dispUpper hδ z m) (summable_norm_disp z m).hasSum (hasSum_dispUpper δ z m)
  refine le_trans h_le ?_
  have h_eq : (∑ j ∈ range (m + 1), dispConst z δ ^ 2 * ((1 + δ) ^ 2) ^ m * (1 / 2 : ℝ) ^ (m - j) * 2) =
      2 * dispConst z δ ^ 2 * ((1 + δ) ^ 2) ^ m * (∑ j ∈ range (m + 1), (1 / 2 : ℝ) ^ (m - j)) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro j _
    ring
  rw [h_eq]
  have hc_pos : 0 ≤ dispConst z δ := (dispConst_pos z δ).le
  calc 2 * dispConst z δ ^ 2 * ((1 + δ) ^ 2) ^ m * (∑ j ∈ range (m + 1), (1 / 2 : ℝ) ^ (m - j))
      ≤ 2 * dispConst z δ ^ 2 * ((1 + δ) ^ 2) ^ m * 2 :=
        mul_le_mul_of_nonneg_left (sum_half_pow_sub_le m) (by positivity)
    _ = 4 * dispConst z δ ^ 2 * ((1 + δ) ^ 2) ^ m := by ring

lemma summable_mul_prod {α β : Type*} (u : α → ℝ) (v : β → ℝ)
    (hu0 : ∀ a, 0 ≤ u a) (hv0 : ∀ b, 0 ≤ v b) (hu : Summable u) (hv : Summable v) :
    Summable (fun p : α × β => u p.1 * v p.2) := by
  rw [summable_prod_of_nonneg (fun p => mul_nonneg (hu0 p.1) (hv0 p.2))]
  refine ⟨fun a => hv.mul_left (u a), ?_⟩
  have h_eq : (fun a => ∑' b, u a * v b) = fun a => u a * (∑' b, v b) := by
    funext a
    exact tsum_mul_left
  rw [h_eq]
  exact hu.mul_right (∑' b, v b)

lemma tsum_mul_prod {α β : Type*} (u : α → ℝ) (v : β → ℝ)
    (hu0 : ∀ a, 0 ≤ u a) (hv0 : ∀ b, 0 ≤ v b) (hu : Summable u) (hv : Summable v) :
    (∑' p : α × β, u p.1 * v p.2) = (∑' a, u a) * (∑' b, v b) := by
  rw [(summable_mul_prod u v hu0 hv0 hu hv).tsum_prod]
  have h_eq : (fun a => ∑' b, u a * v b) = fun a => u a * (∑' b, v b) := by
    funext a
    exact tsum_mul_left
  rw [h_eq, tsum_mul_right]

lemma tsum_comm_of_summable {α β γ : Type*} [NormedAddCommGroup γ] [CompleteSpace γ]
    (f : α × β → γ) (hf : Summable f) :
    (∑' a : α, ∑' b : β, f (a, b)) = ∑' b : β, ∑' a : α, f (a, b) := by
  have hsw := (Equiv.prodComm β α).summable_iff.mpr hf
  rw [← hf.tsum_prod, ← (Equiv.prodComm β α).tsum_eq f]
  exact hsw.tsum_prod

lemma summable_ite_le_prod_real (r : ℕ) (g : ℕ × ℕ → ℝ) (hg0 : ∀ p, 0 ≤ g p) (hg : Summable g) :
    Summable (fun p : ℕ × ℕ => if r ≤ p.1 ∧ r ≤ p.2 then g (p.1 - r, p.2 - r) else 0) := by
  have h_row : ∀ j : ℕ, HasSum (fun k : ℕ => if r ≤ j ∧ r ≤ k then g (j - r, k - r) else 0)
      (if r ≤ j then ∑' k' : ℕ, g (j - r, k') else 0) := by
    intro j
    by_cases hrj : r ≤ j
    · have h_eq : (fun k : ℕ => if r ≤ j ∧ r ≤ k then g (j - r, k - r) else 0) =
          fun k : ℕ => if r ≤ k then g (j - r, k - r) else 0 := by
        funext k; simp [hrj]
      rw [h_eq, if_pos hrj]
      exact hasSum_ite_le_real r (fun k' => g (j - r, k')) (hg.prod_factor (j - r)).hasSum
    · have h_eq : (fun k : ℕ => if r ≤ j ∧ r ≤ k then g (j - r, k - r) else 0) = fun _ => 0 := by
        funext k; simp [hrj]
      rw [h_eq, if_neg hrj]
      exact hasSum_zero
  have h_nn : ∀ p : ℕ × ℕ, 0 ≤ (if r ≤ p.1 ∧ r ≤ p.2 then g (p.1 - r, p.2 - r) else 0) := by
    intro p
    split_ifs
    · exact hg0 _
    · exact le_rfl
  rw [summable_prod_of_nonneg h_nn]
  refine ⟨fun j => (h_row j).summable, ?_⟩
  have h_tsum : (fun j : ℕ => ∑' k : ℕ, if r ≤ j ∧ r ≤ k then g (j - r, k - r) else 0) =
      fun j : ℕ => if r ≤ j then ∑' k' : ℕ, g (j - r, k') else 0 :=
    funext (fun j => (h_row j).tsum_eq)
  rw [h_tsum]
  exact (hasSum_ite_le_real r (fun j' => ∑' k' : ℕ, g (j', k')) hg.prod.hasSum).summable

lemma tsum_ite_le_prod_real (r : ℕ) (g : ℕ × ℕ → ℝ) (hg0 : ∀ p, 0 ≤ g p) (hg : Summable g) :
    (∑' p : ℕ × ℕ, if r ≤ p.1 ∧ r ≤ p.2 then g (p.1 - r, p.2 - r) else 0) =
      ∑' q : ℕ × ℕ, g q := by
  have h_shift := summable_ite_le_prod_real r g hg0 hg
  have h_row : ∀ j : ℕ, HasSum (fun k : ℕ => if r ≤ j ∧ r ≤ k then g (j - r, k - r) else 0)
      (if r ≤ j then ∑' k' : ℕ, g (j - r, k') else 0) := by
    intro j
    by_cases hrj : r ≤ j
    · have h_eq : (fun k : ℕ => if r ≤ j ∧ r ≤ k then g (j - r, k - r) else 0) =
          fun k : ℕ => if r ≤ k then g (j - r, k - r) else 0 := by
        funext k; simp [hrj]
      rw [h_eq, if_pos hrj]
      exact hasSum_ite_le_real r (fun k' => g (j - r, k')) (hg.prod_factor (j - r)).hasSum
    · have h_eq : (fun k : ℕ => if r ≤ j ∧ r ≤ k then g (j - r, k - r) else 0) = fun _ => 0 := by
        funext k; simp [hrj]
      rw [h_eq, if_neg hrj]
      exact hasSum_zero
  rw [h_shift.tsum_prod]
  have h_tsum : (fun j : ℕ => ∑' k : ℕ, if r ≤ j ∧ r ≤ k then g (j - r, k - r) else 0) =
      fun j : ℕ => if r ≤ j then ∑' k' : ℕ, g (j - r, k') else 0 :=
    funext (fun j => (h_row j).tsum_eq)
  rw [h_tsum, (hasSum_ite_le_real r (fun j' => ∑' k' : ℕ, g (j', k')) hg.prod.hasSum).tsum_eq,
    ← hg.tsum_prod]

lemma tsum_ite_le_prod (r : ℕ) (f : ℕ × ℕ → ℂ) (hf : Summable f)
    (hf_shift : Summable (fun p : ℕ × ℕ => if r ≤ p.1 ∧ r ≤ p.2 then f (p.1 - r, p.2 - r) else 0)) :
    (∑' p : ℕ × ℕ, if r ≤ p.1 ∧ r ≤ p.2 then f (p.1 - r, p.2 - r) else 0) =
      ∑' q : ℕ × ℕ, f q := by
  have h_row : ∀ j : ℕ, HasSum (fun k : ℕ => if r ≤ j ∧ r ≤ k then f (j - r, k - r) else 0)
      (if r ≤ j then ∑' k' : ℕ, f (j - r, k') else 0) := by
    intro j
    by_cases hrj : r ≤ j
    · have h_eq : (fun k : ℕ => if r ≤ j ∧ r ≤ k then f (j - r, k - r) else 0) =
          fun k : ℕ => if r ≤ k then f (j - r, k - r) else 0 := by
        funext k; simp [hrj]
      rw [h_eq, if_pos hrj]
      exact hasSum_ite_le r (fun k' => f (j - r, k')) (hf.prod_factor (j - r)).hasSum
    · have h_eq : (fun k : ℕ => if r ≤ j ∧ r ≤ k then f (j - r, k - r) else 0) = fun _ => 0 := by
        funext k; simp [hrj]
      rw [h_eq, if_neg hrj]
      exact hasSum_zero
  rw [hf_shift.tsum_prod]
  have h_tsum : (fun j : ℕ => ∑' k : ℕ, if r ≤ j ∧ r ≤ k then f (j - r, k - r) else 0) =
      fun j : ℕ => if r ≤ j then ∑' k' : ℕ, f (j - r, k') else 0 :=
    funext (fun j => (h_row j).tsum_eq)
  rw [h_tsum, (hasSum_ite_le r (fun j' => ∑' k' : ℕ, f (j', k')) hf.prod.hasSum).tsum_eq,
    ← hf.tsum_prod]

lemma termX_eq (e : ℝ) (ρ : ℕ → ℕ → ℂ) (m n l : ℕ) :
    vacuumLossTerm e ρ m n l = (lcoefX e m n l : ℂ) * ρ (m + l) (n + l) := rfl

lemma lcoefX_nonneg {e : ℝ} (he1 : e ≤ 1) (m n l : ℕ) : 0 ≤ lcoefX e m n l := by
  unfold lcoefX
  have : 0 ≤ (1 - e) ^ l := pow_nonneg (by linarith) _
  positivity

lemma lcoefX_mul_pow_summable {e q : ℝ} (he0 : 0 < e) (he1 : e < 1) (hq0 : 0 ≤ q)
    (heq : (1 - e) * q < 1) (m n : ℕ) :
    Summable (fun l : ℕ => lcoefX e m n l * q ^ l) := by
  have hr0 : 0 ≤ (1 - e) * q := mul_nonneg (by linarith) hq0
  have hr : ‖(1 - e) * q‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hr0]
    exact heq
  have h1 := summable_choose_mul_geometric_of_norm_lt_one (R := ℝ) m hr
  have h2 := summable_choose_mul_geometric_of_norm_lt_one (R := ℝ) n hr
  refine Summable.of_nonneg_of_le (fun l => mul_nonneg (lcoefX_nonneg he1.le m n l) (pow_nonneg hq0 l))
    (fun l => ?_) (h1.add h2)
  have hc1 : ((m + l).choose l : ℝ) = ((l + m).choose m : ℝ) := by
    rw [add_comm m l, Nat.choose_symm_add]
  have hc2 : ((n + l).choose l : ℝ) = ((l + n).choose n : ℝ) := by
    rw [add_comm n l, Nat.choose_symm_add]
  have hs : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → Real.sqrt a * Real.sqrt b ≤ a + b := by
    intro a b ha hb
    nlinarith [sq_nonneg (Real.sqrt a - Real.sqrt b), Real.sq_sqrt ha, Real.sq_sqrt hb,
      Real.sqrt_nonneg a, Real.sqrt_nonneg b]
  have hse : Real.sqrt e ≤ 1 := Real.sqrt_le_one.mpr he1.le
  have hp : Real.sqrt e ^ m * Real.sqrt e ^ n ≤ 1 :=
    mul_le_one₀ (pow_le_one₀ (Real.sqrt_nonneg _) hse) (by positivity)
      (pow_le_one₀ (Real.sqrt_nonneg _) hse)
  have hq : 0 ≤ ((1 - e) * q) ^ l := pow_nonneg hr0 _
  calc lcoefX e m n l * q ^ l
      = (Real.sqrt ((m + l).choose l : ℝ) * Real.sqrt ((n + l).choose l : ℝ)) *
          (Real.sqrt e ^ m * Real.sqrt e ^ n) * ((1 - e) * q) ^ l := by
        unfold lcoefX; rw [mul_pow]; ring
    _ ≤ (((m + l).choose l : ℝ) + ((n + l).choose l : ℝ)) * 1 * ((1 - e) * q) ^ l := by
        apply mul_le_mul_of_nonneg_right _ hq
        exact mul_le_mul (hs ((m + l).choose l : ℝ) ((n + l).choose l : ℝ) (by positivity) (by positivity))
          hp (by positivity) (by positivity)
    _ = _ := by rw [hc1, hc2]; ring

lemma lcoefX_summable {e : ℝ} (he0 : 0 < e) (he1 : e < 1) (m n : ℕ) :
    Summable (lcoefX e m n) := by
  simpa using lcoefX_mul_pow_summable he0 he1 zero_le_one (by linarith) m n

lemma tsum_lcoefX_le {e : ℝ} (he0 : 0 < e) (he1 : e < 1) (m n : ℕ) :
    (∑' l : ℕ, lcoefX e m n l) ≤ 2 / e := by
  have hr : ‖1 - e‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (by linarith)]
    linarith
  have h_has : ∀ k : ℕ, HasSum (fun l : ℕ => e ^ k * (((l + k).choose k : ℝ) * (1 - e) ^ l)) (1 / e) := by
    intro k
    have h1 := (hasSum_choose_mul_geometric_of_norm_lt_one (𝕜 := ℝ) k hr).mul_left (e ^ k)
    have h_eq : e ^ k * (1 / (1 - (1 - e)) ^ (k + 1)) = 1 / e := by
      have he_sub : 1 - (1 - e) = e := by ring
      have he_ne : e ≠ 0 := he0.ne'
      rw [he_sub, pow_succ]
      field_simp
    rwa [h_eq] at h1
  have h_le : ∀ l : ℕ, lcoefX e m n l ≤
      e ^ m * (((l + m).choose m : ℝ) * (1 - e) ^ l) +
      e ^ n * (((l + n).choose n : ℝ) * (1 - e) ^ l) := by
    intro l
    let A := e ^ m * (((l + m).choose m : ℝ) * (1 - e) ^ l)
    let B := e ^ n * (((l + n).choose n : ℝ) * (1 - e) ^ l)
    have hA0 : 0 ≤ A := by dsimp only [A]; have : 0 ≤ (1 - e) ^ l := pow_nonneg (by linarith) l; positivity
    have hB0 : 0 ≤ B := by dsimp only [B]; have : 0 ≤ (1 - e) ^ l := pow_nonneg (by linarith) l; positivity
    have hc1 : ((m + l).choose l : ℝ) = ((l + m).choose m : ℝ) := by
      rw [add_comm m l, Nat.choose_symm_add]
    have hc2 : ((n + l).choose l : ℝ) = ((l + n).choose n : ℝ) := by
      rw [add_comm n l, Nat.choose_symm_add]
    have h_sq_eq : (lcoefX e m n l) ^ 2 = A * B := by
      dsimp only [lcoefX, A, B]
      rw [hc1, hc2]
      calc (Real.sqrt ((l + m).choose m : ℝ) * Real.sqrt ((l + n).choose n : ℝ) *
              Real.sqrt e ^ m * Real.sqrt e ^ n * (1 - e) ^ l) ^ 2
          = (Real.sqrt ((l + m).choose m : ℝ) ^ 2) * (Real.sqrt ((l + n).choose n : ℝ) ^ 2) *
              ((Real.sqrt e ^ 2) ^ m) * ((Real.sqrt e ^ 2) ^ n) * ((1 - e) ^ l) ^ 2 := by ring
        _ = (e ^ m * (((l + m).choose m : ℝ) * (1 - e) ^ l)) *
              (e ^ n * (((l + n).choose n : ℝ) * (1 - e) ^ l)) := by
            rw [Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity), Real.sq_sqrt he0.le]
            ring
    have h_sq_le : (lcoefX e m n l) ^ 2 ≤ (A + B) ^ 2 := by
      nlinarith [sq_nonneg (A - B)]
    exact (abs_le_of_sq_le_sq' h_sq_le (by positivity)).2
  have h_sum_le := hasSum_le h_le (lcoefX_summable he0 he1 m n).hasSum ((h_has m).add (h_has n))
  have h_two : 1 / e + 1 / e = 2 / e := by ring
  linarith

lemma summable_dispConjTerm_of_bounded {K : ℕ → ℕ → ℂ} {B : ℝ} (hB0 : 0 ≤ B)
    (hK : ∀ j k, ‖K j k‖ ≤ B) (β : ℂ) (a b : ℕ) :
    Summable (dispConjTerm β K a b) := by
  have hg : Summable (fun p : ℕ × ℕ => (B * ‖displacementMatrix β a p.1‖) * ‖displacementMatrix β b p.2‖) :=
    summable_mul_prod (fun j => B * ‖displacementMatrix β a j‖) (fun k => ‖displacementMatrix β b k‖)
      (fun j => mul_nonneg hB0 (norm_nonneg _)) (fun k => norm_nonneg _)
      ((summable_norm_disp β a).mul_left B) (summable_norm_disp β b)
  refine Summable.of_norm_bounded hg (fun p => ?_)
  dsimp only [dispConjTerm]
  rw [norm_mul, norm_mul, norm_star]
  calc ‖displacementMatrix β a p.1‖ * ‖K p.1 p.2‖ * ‖displacementMatrix β b p.2‖
      ≤ ‖displacementMatrix β a p.1‖ * B * ‖displacementMatrix β b p.2‖ := by
        gcongr; exact hK p.1 p.2
    _ = (B * ‖displacementMatrix β a p.1‖) * ‖displacementMatrix β b p.2‖ := by ring

lemma summable_vacuumLossTerm_of_bounded {η : ℝ} (hη0 : 0 < η) (hη1 : η < 1)
    {K : ℕ → ℕ → ℂ} {B : ℝ} (hK : ∀ j k, ‖K j k‖ ≤ B) (a b : ℕ) :
    Summable (vacuumLossTerm η K a b) := by
  refine Summable.of_norm_bounded ((lcoefX_summable hη0 hη1 a b).mul_left B) (fun l => ?_)
  rw [termX_eq, norm_mul, Complex.norm_real, Real.norm_of_nonneg (lcoefX_nonneg hη1.le a b l), mul_comm]
  exact mul_le_mul_of_nonneg_right (hK _ _) (lcoefX_nonneg hη1.le a b l)

lemma norm_vacuumLossKernel_le_of_bounded {η : ℝ} (hη0 : 0 < η) (hη1 : η < 1)
    {K : ℕ → ℕ → ℂ} {B : ℝ} (hB0 : 0 ≤ B) (hK : ∀ j k, ‖K j k‖ ≤ B) (a b : ℕ) :
    ‖vacuumLossKernel η K a b‖ ≤ B * (2 / η) := by
  unfold vacuumLossKernel
  have h_sum_norm : Summable (fun l : ℕ => ‖vacuumLossTerm η K a b l‖) :=
    (summable_vacuumLossTerm_of_bounded hη0 hη1 hK a b).norm
  refine le_trans (norm_tsum_le_tsum_norm h_sum_norm) ?_
  have h_le : ∀ l : ℕ, ‖vacuumLossTerm η K a b l‖ ≤ B * lcoefX η a b l := by
    intro l
    rw [termX_eq, norm_mul, Complex.norm_real, Real.norm_of_nonneg (lcoefX_nonneg hη1.le a b l), mul_comm]
    exact mul_le_mul_of_nonneg_right (hK _ _) (lcoefX_nonneg hη1.le a b l)
  have h_tsum_le := hasSum_le h_le h_sum_norm.hasSum ((lcoefX_summable hη0 hη1 a b).hasSum.mul_left B)
  refine le_trans h_tsum_le ?_
  exact mul_le_mul_of_nonneg_left (tsum_lcoefX_le hη0 hη1 a b) hB0

lemma eta_delta_pow_lt_one {η : ℝ} (hη0 : 0 < η) (hη1 : η < 1) :
    (1 - η) * (1 + η / 10) ^ 4 < 1 := by
  have hδ0 : 0 < η / 10 := by linarith
  have hδ1 : η / 10 ≤ 1 / 10 := by linarith
  have hδ_sq : (η / 10) * (η / 10) ≤ (1 / 10) * (η / 10) :=
    mul_le_mul_of_nonneg_right hδ1 hδ0.le
  have h1 : (1 + η / 10) ^ 2 ≤ 1 + 3 * (η / 10) := by nlinarith
  have h2 : (1 + 3 * (η / 10)) ^ 2 ≤ 1 + η := by nlinarith
  have h3 : (1 + η / 10) ^ 4 ≤ 1 + η := by
    have h_pow : (1 + η / 10) ^ 4 = ((1 + η / 10) ^ 2) ^ 2 := by ring
    rw [h_pow]
    have h_sq_le : ((1 + η / 10) ^ 2) ^ 2 ≤ (1 + 3 * (η / 10)) ^ 2 :=
      pow_le_pow_left₀ (by positivity) h1 2
    linarith
  have h4 : (1 - η) * (1 + η / 10) ^ 4 ≤ (1 - η) * (1 + η) :=
    mul_le_mul_of_nonneg_left h3 (by linarith)
  nlinarith [sq_pos_of_pos hη0]

noncomputable def lossDispF1 (η : ℝ) (β : ℂ) (K : ℕ → ℕ → ℂ) (m n : ℕ) (x : ℕ × (ℕ × ℕ)) : ℂ :=
  (lcoefX η m n x.1 : ℂ) * dispConjTerm β K (m + x.1) (n + x.1) x.2

lemma summable_lossDispF1 {η : ℝ} (hη0 : 0 < η) (hη1 : η < 1)
    {K : ℕ → ℕ → ℂ} {B : ℝ} (hB0 : 0 ≤ B) (hK : ∀ j k, ‖K j k‖ ≤ B) (β : ℂ) (m n : ℕ) :
    Summable (lossDispF1 η β K m n) := by
  have hg1_0 : ∀ x : ℕ × (ℕ × ℕ),
      0 ≤ lcoefX η m n x.1 * ((B * ‖displacementMatrix β (m + x.1) x.2.1‖) * ‖displacementMatrix β (n + x.1) x.2.2‖) := by
    intro x
    exact mul_nonneg (lcoefX_nonneg hη1.le m n x.1)
      (mul_nonneg (mul_nonneg hB0 (norm_nonneg (displacementMatrix β (m + x.1) x.2.1)))
        (norm_nonneg (displacementMatrix β (n + x.1) x.2.2)))
  have hg1 : Summable (fun x : ℕ × (ℕ × ℕ) =>
      lcoefX η m n x.1 * ((B * ‖displacementMatrix β (m + x.1) x.2.1‖) * ‖displacementMatrix β (n + x.1) x.2.2‖)) := by
    rw [summable_prod_of_nonneg hg1_0]
    have h_row : ∀ ell : ℕ, Summable (fun p : ℕ × ℕ =>
        lcoefX η m n ell * ((B * ‖displacementMatrix β (m + ell) p.1‖) * ‖displacementMatrix β (n + ell) p.2‖)) := fun ell =>
      (summable_mul_prod
        (fun j => B * ‖displacementMatrix β (m + ell) j‖)
        (fun k => ‖displacementMatrix β (n + ell) k‖)
        (fun j => mul_nonneg hB0 (norm_nonneg (displacementMatrix β (m + ell) j)))
        (fun k => norm_nonneg (displacementMatrix β (n + ell) k))
        ((summable_norm_disp β (m + ell)).mul_left B)
        (summable_norm_disp β (n + ell))).mul_left (lcoefX η m n ell)
    refine ⟨h_row, ?_⟩
    let δ := η / 10
    have hδ0 : 0 < δ := by dsimp only [δ]; linarith
    let C_m_n := B * 16 * dispConst β δ ^ 4 * ((1 + δ) ^ 2) ^ m * ((1 + δ) ^ 2) ^ n
    have h_sum_ell : Summable (fun ell : ℕ => C_m_n * (lcoefX η m n ell * ((1 + δ) ^ 4) ^ ell)) :=
      (lcoefX_mul_pow_summable hη0 hη1 (by positivity) (eta_delta_pow_lt_one hη0 hη1) m n).mul_left C_m_n
    refine Summable.of_nonneg_of_le (fun ell => tsum_nonneg (fun p => hg1_0 (ell, p))) (fun ell => ?_) h_sum_ell
    dsimp only
    rw [tsum_mul_left, tsum_mul_prod
      (fun j => B * ‖displacementMatrix β (m + ell) j‖)
      (fun k => ‖displacementMatrix β (n + ell) k‖)
      (fun j => mul_nonneg hB0 (norm_nonneg (displacementMatrix β (m + ell) j)))
      (fun k => norm_nonneg (displacementMatrix β (n + ell) k))
      ((summable_norm_disp β (m + ell)).mul_left B) (summable_norm_disp β (n + ell)), tsum_mul_left]
    have h_d1 := tsum_norm_disp_le hδ0 β (m + ell)
    have h_d2 := tsum_norm_disp_le hδ0 β (n + ell)
    have hc_pos : 0 ≤ dispConst β δ := (dispConst_pos β δ).le
    calc lcoefX η m n ell * (B * (∑' j, ‖displacementMatrix β (m + ell) j‖) * (∑' k, ‖displacementMatrix β (n + ell) k‖))
        ≤ lcoefX η m n ell * (B * (4 * dispConst β δ ^ 2 * ((1 + δ) ^ 2) ^ (m + ell)) *
            (4 * dispConst β δ ^ 2 * ((1 + δ) ^ 2) ^ (n + ell))) := by
          apply mul_le_mul_of_nonneg_left _ (lcoefX_nonneg hη1.le m n ell)
          exact mul_le_mul (mul_le_mul_of_nonneg_left h_d1 hB0) h_d2 (tsum_nonneg (fun j => norm_nonneg (displacementMatrix β (n + ell) j))) (by positivity)
      _ = C_m_n * (lcoefX η m n ell * ((1 + δ) ^ 4) ^ ell) := by
          dsimp only [C_m_n]
          rw [pow_add ((1 + δ) ^ 2) m ell, pow_add ((1 + δ) ^ 2) n ell,
            show (1 + δ) ^ 4 = ((1 + δ) ^ 2) * ((1 + δ) ^ 2) by ring, mul_pow]
          ring
  refine Summable.of_norm_bounded hg1 (fun x => ?_)
  dsimp only [lossDispF1, dispConjTerm]
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (lcoefX_nonneg hη1.le m n x.1),
    norm_mul, norm_mul, norm_star]
  apply mul_le_mul_of_nonneg_left _ (lcoefX_nonneg hη1.le m n x.1)
  calc ‖displacementMatrix β (m + x.1) x.2.1‖ * ‖K x.2.1 x.2.2‖ * ‖displacementMatrix β (n + x.1) x.2.2‖
      ≤ ‖displacementMatrix β (m + x.1) x.2.1‖ * B * ‖displacementMatrix β (n + x.1) x.2.2‖ := by
        gcongr; exact hK x.2.1 x.2.2
    _ = (B * ‖displacementMatrix β (m + x.1) x.2.1‖) * ‖displacementMatrix β (n + x.1) x.2.2‖ := by ring

noncomputable def lossDispH2 (η : ℝ) (z2 : ℂ) (K : ℕ → ℕ → ℂ) (m n : ℕ) (x : ℕ × (ℕ × ℕ)) : ℂ :=
  displacementMatrix z2 m x.2.1 * ((lcoefX η x.2.1 x.2.2 x.1 : ℂ) * K (x.2.1 + x.1) (x.2.2 + x.1)) *
    star (displacementMatrix z2 n x.2.2)

noncomputable def lossDispG2 (η : ℝ) (z2 : ℂ) (K : ℕ → ℕ → ℂ) (m n : ℕ) (x : ℕ × (ℕ × ℕ)) : ℂ :=
  if x.1 ≤ x.2.1 ∧ x.1 ≤ x.2.2 then lossDispH2 η z2 K m n (x.1, (x.2.1 - x.1, x.2.2 - x.1)) else 0

noncomputable def lossDispH2Bound (η B : ℝ) (z2 : ℂ) (m n : ℕ) (x : ℕ × (ℕ × ℕ)) : ℝ :=
  lcoefX η x.2.1 x.2.2 x.1 * ((B * ‖displacementMatrix z2 m x.2.1‖) * ‖displacementMatrix z2 n x.2.2‖)

lemma lossDispH2Bound_nonneg {η B : ℝ} (hη1 : η ≤ 1) (hB0 : 0 ≤ B) (z2 : ℂ) (m n : ℕ) (x : ℕ × (ℕ × ℕ)) :
    0 ≤ lossDispH2Bound η B z2 m n x := by
  dsimp only [lossDispH2Bound]
  exact mul_nonneg (lcoefX_nonneg hη1 x.2.1 x.2.2 x.1)
    (mul_nonneg (mul_nonneg hB0 (norm_nonneg (displacementMatrix z2 m x.2.1)))
      (norm_nonneg (displacementMatrix z2 n x.2.2)))

lemma summable_lossDispH2Bound {η B : ℝ} (hη0 : 0 < η) (hη1 : η < 1) (hB0 : 0 ≤ B) (z2 : ℂ) (m n : ℕ) :
    Summable (lossDispH2Bound η B z2 m n) := by
  have hsw : Summable (fun y : (ℕ × ℕ) × ℕ => lossDispH2Bound η B z2 m n y.swap) := by
    rw [summable_prod_of_nonneg (fun y => lossDispH2Bound_nonneg hη1.le hB0 z2 m n y.swap)]
    refine ⟨fun q => (lcoefX_summable hη0 hη1 q.1 q.2).mul_right
      ((B * ‖displacementMatrix z2 m q.1‖) * ‖displacementMatrix z2 n q.2‖), ?_⟩
    have h_q_bound : Summable (fun q : ℕ × ℕ => (2 / η) * ((B * ‖displacementMatrix z2 m q.1‖) * ‖displacementMatrix z2 n q.2‖)) :=
      (summable_mul_prod
        (fun j => B * ‖displacementMatrix z2 m j‖)
        (fun k => ‖displacementMatrix z2 n k‖)
        (fun j => mul_nonneg hB0 (norm_nonneg (displacementMatrix z2 m j)))
        (fun k => norm_nonneg (displacementMatrix z2 n k))
        ((summable_norm_disp z2 m).mul_left B) (summable_norm_disp z2 n)).mul_left (2 / η)
    refine Summable.of_nonneg_of_le (fun q => tsum_nonneg (fun r => lossDispH2Bound_nonneg hη1.le hB0 z2 m n (r, q)))
      (fun q => ?_) h_q_bound
    dsimp only [Prod.swap, lossDispH2Bound]
    rw [tsum_mul_right]
    exact mul_le_mul_of_nonneg_right (tsum_lcoefX_le hη0 hη1 q.1 q.2)
      (mul_nonneg (mul_nonneg hB0 (norm_nonneg (displacementMatrix z2 m q.1)))
        (norm_nonneg (displacementMatrix z2 n q.2)))
  exact (Equiv.prodComm (ℕ × ℕ) ℕ).summable_iff.mp hsw

lemma summable_lossDispH2 {η : ℝ} (hη0 : 0 < η) (hη1 : η < 1)
    {K : ℕ → ℕ → ℂ} {B : ℝ} (hB0 : 0 ≤ B) (hK : ∀ j k, ‖K j k‖ ≤ B) (z2 : ℂ) (m n : ℕ) :
    Summable (lossDispH2 η z2 K m n) := by
  refine Summable.of_norm_bounded (summable_lossDispH2Bound hη0 hη1 hB0 z2 m n) (fun x => ?_)
  dsimp only [lossDispH2, lossDispH2Bound]
  rw [norm_mul, norm_mul, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (lcoefX_nonneg hη1.le x.2.1 x.2.2 x.1), norm_star]
  calc ‖displacementMatrix z2 m x.2.1‖ * (lcoefX η x.2.1 x.2.2 x.1 * ‖K (x.2.1 + x.1) (x.2.2 + x.1)‖) *
          ‖displacementMatrix z2 n x.2.2‖
      ≤ ‖displacementMatrix z2 m x.2.1‖ * (lcoefX η x.2.1 x.2.2 x.1 * B) *
          ‖displacementMatrix z2 n x.2.2‖ := by
        gcongr
        · exact lcoefX_nonneg hη1.le _ _ _
        · exact hK _ _
    _ = lcoefX η x.2.1 x.2.2 x.1 * ((B * ‖displacementMatrix z2 m x.2.1‖) * ‖displacementMatrix z2 n x.2.2‖) := by ring

lemma summable_lossDispG2 {η : ℝ} (hη0 : 0 < η) (hη1 : η < 1)
    {K : ℕ → ℕ → ℂ} {B : ℝ} (hB0 : 0 ≤ B) (hK : ∀ j k, ‖K j k‖ ≤ B) (z2 : ℂ) (m n : ℕ) :
    Summable (lossDispG2 η z2 K m n) := by
  have hh2_sum := summable_lossDispH2Bound hη0 hη1 hB0 z2 m n
  let g2_b : ℕ × (ℕ × ℕ) → ℝ := fun x =>
    if x.1 ≤ x.2.1 ∧ x.1 ≤ x.2.2 then lossDispH2Bound η B z2 m n (x.1, (x.2.1 - x.1, x.2.2 - x.1)) else 0
  have hg2_0 : ∀ x, 0 ≤ g2_b x := by
    intro x
    dsimp only [g2_b]
    split_ifs
    · exact lossDispH2Bound_nonneg hη1.le hB0 z2 m n _
    · exact le_rfl
  have hg2_sum : Summable g2_b := by
    rw [summable_prod_of_nonneg hg2_0]
    refine ⟨fun r => summable_ite_le_prod_real r (fun q => lossDispH2Bound η B z2 m n (r, q))
      (fun q => lossDispH2Bound_nonneg hη1.le hB0 z2 m n (r, q)) (hh2_sum.prod_factor r), ?_⟩
    have h_eq : (fun r : ℕ => ∑' p : ℕ × ℕ, g2_b (r, p)) =
        fun r : ℕ => ∑' q : ℕ × ℕ, lossDispH2Bound η B z2 m n (r, q) := by
      funext r
      exact tsum_ite_le_prod_real r (fun q => lossDispH2Bound η B z2 m n (r, q))
        (fun q => lossDispH2Bound_nonneg hη1.le hB0 z2 m n (r, q)) (hh2_sum.prod_factor r)
    rw [h_eq]
    exact hh2_sum.prod
  refine Summable.of_norm_bounded hg2_sum (fun x => ?_)
  dsimp only [lossDispG2, g2_b]
  split_ifs with hx
  · dsimp only [lossDispH2, lossDispH2Bound]
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (lcoefX_nonneg hη1.le _ _ _), norm_star]
    calc ‖displacementMatrix z2 m (x.2.1 - x.1)‖ *
            (lcoefX η (x.2.1 - x.1) (x.2.2 - x.1) x.1 * ‖K (x.2.1 - x.1 + x.1) (x.2.2 - x.1 + x.1)‖) *
            ‖displacementMatrix z2 n (x.2.2 - x.1)‖
        ≤ ‖displacementMatrix z2 m (x.2.1 - x.1)‖ *
            (lcoefX η (x.2.1 - x.1) (x.2.2 - x.1) x.1 * B) *
            ‖displacementMatrix z2 n (x.2.2 - x.1)‖ := by
          gcongr
          · exact lcoefX_nonneg hη1.le _ _ _
          · exact hK _ _
      _ = lcoefX η (x.2.1 - x.1) (x.2.2 - x.1) x.1 *
            ((B * ‖displacementMatrix z2 m (x.2.1 - x.1)‖) * ‖displacementMatrix z2 n (x.2.2 - x.1)‖) := by ring
  · simp

lemma lossDisp_p_eq {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (β : ℂ) (K : ℕ → ℕ → ℂ) (m n : ℕ) (p : ℕ × ℕ) :
    (∑' ell : ℕ, lossDispF1 η β K m n (ell, p)) =
      ∑' r : ℕ, lossDispG2 η (((Real.sqrt η : ℝ) : ℂ) * β) K m n (r, p) := by
  have h_f1 : (fun ell : ℕ => lossDispF1 η β K m n (ell, p)) =
      fun ell : ℕ => ((lcoefX η m n ell : ℂ) * displacementMatrix β (m + ell) p.1 *
        star (displacementMatrix β (n + ell) p.2)) * K p.1 p.2 := by
    funext ell
    dsimp only [lossDispF1, dispConjTerm]
    ring
  rw [h_f1, ((hasSum_loss_disp_entry hη0 hη1 β m n p.1 p.2).mul_right (K p.1 p.2)).tsum_eq,
    sum_mul]
  rw [tsum_eq_sum (s := range (min p.1 p.2 + 1))]
  · apply sum_congr rfl
    intro r hr
    rw [mem_range] at hr
    have hrp : r ≤ p.1 ∧ r ≤ p.2 := by omega
    dsimp only [lossDispG2, lossDispH2]
    rw [if_pos hrp, Nat.sub_add_cancel hrp.1, Nat.sub_add_cancel hrp.2]
    ring
  · intro r hr
    rw [mem_range] at hr
    have hrp : ¬ (r ≤ p.1 ∧ r ≤ p.2) := by omega
    dsimp only [lossDispG2]
    rw [if_neg hrp]

theorem eq_18_of_bounded {η : ℝ} (hη0 : 0 < η) (hη1 : η < 1)
    {K : ℕ → ℕ → ℂ} {B : ℝ} (hB0 : 0 ≤ B) (hK : ∀ j k, ‖K j k‖ ≤ B) (β : ℂ) :
    (∀ a b : ℕ, Summable (dispConjTerm β K a b)) ∧
    (∀ a b : ℕ, Summable (vacuumLossTerm η (dispConj β K) a b)) ∧
    (∀ a b : ℕ, Summable (vacuumLossTerm η K a b)) ∧
    (∀ a b : ℕ, Summable (dispConjTerm (((Real.sqrt η : ℝ) : ℂ) * β) (vacuumLossKernel η K) a b)) ∧
    ∀ m n : ℕ, vacuumLossKernel η (dispConj β K) m n =
      dispConj (((Real.sqrt η : ℝ) : ℂ) * β) (vacuumLossKernel η K) m n := by
  have hF1_row : ∀ m n ell, vacuumLossTerm η (dispConj β K) m n ell =
      ∑' p : ℕ × ℕ, lossDispF1 η β K m n (ell, p) := by
    intro m n ell
    rw [termX_eq, dispConj, ← tsum_mul_left]
    rfl
  refine ⟨summable_dispConjTerm_of_bounded hB0 hK β,
    fun a b => by rw [funext (hF1_row a b)]; exact (summable_lossDispF1 hη0 hη1 hB0 hK β a b).prod,
    summable_vacuumLossTerm_of_bounded hη0 hη1 hK,
    summable_dispConjTerm_of_bounded (mul_nonneg hB0 (by positivity))
      (norm_vacuumLossKernel_le_of_bounded hη0 hη1 hB0 hK) (((Real.sqrt η : ℝ) : ℂ) * β),
    fun m n => ?_⟩
  let z2 : ℂ := ((Real.sqrt η : ℝ) : ℂ) * β
  have hF1 := summable_lossDispF1 hη0 hη1 hB0 hK β m n
  have hH2 := summable_lossDispH2 hη0 hη1 hB0 hK z2 m n
  have hG2 := summable_lossDispG2 hη0 hη1 hB0 hK z2 m n
  have h_r_eq : ∀ r : ℕ, (∑' p : ℕ × ℕ, lossDispG2 η z2 K m n (r, p)) =
      ∑' q : ℕ × ℕ, lossDispH2 η z2 K m n (r, q) :=
    fun r => tsum_ite_le_prod r (fun q => lossDispH2 η z2 K m n (r, q)) (hH2.prod_factor r) (hG2.prod_factor r)
  have h_q_eq : ∀ q : ℕ × ℕ, (∑' r : ℕ, lossDispH2 η z2 K m n (r, q)) =
      dispConjTerm z2 (vacuumLossKernel η K) m n q := by
    intro q
    dsimp only [lossDispH2, dispConjTerm, vacuumLossKernel]
    have h_h2 : (fun r : ℕ => displacementMatrix z2 m q.1 *
          ((lcoefX η q.1 q.2 r : ℂ) * K (q.1 + r) (q.2 + r)) * star (displacementMatrix z2 n q.2)) =
        fun r : ℕ => displacementMatrix z2 m q.1 * vacuumLossTerm η K q.1 q.2 r *
          star (displacementMatrix z2 n q.2) := rfl
    rw [h_h2, tsum_mul_right, tsum_mul_left]
  rw [vacuumLossKernel, tsum_congr (hF1_row m n), tsum_comm_of_summable (lossDispF1 η β K m n) hF1,
    tsum_congr (lossDisp_p_eq hη0.le hη1.le β K m n),
    ← tsum_comm_of_summable (lossDispG2 η z2 K m n) hG2,
    tsum_congr h_r_eq, tsum_comm_of_summable (lossDispH2 η z2 K m n) hH2,
    tsum_congr h_q_eq, dispConj]

theorem solution (η : ℝ) (hη0 : 0 < η) (hη1 : η < 1) (X : FockOperator) (hX : IsDensity X)
    (β : ℂ) :
    let K : ℕ → ℕ → ℂ := fun m n => X (fockKet n) m
    (∀ a b : ℕ, Summable (dispConjTerm β K a b)) ∧
    (∀ a b : ℕ, Summable (vacuumLossTerm η (dispConj β K) a b)) ∧
    (∀ a b : ℕ, Summable (vacuumLossTerm η K a b)) ∧
    (∀ a b : ℕ, Summable (dispConjTerm (((Real.sqrt η : ℝ) : ℂ) * β) (vacuumLossKernel η K) a b)) ∧
    ∀ m n : ℕ, vacuumLossKernel η (dispConj β K) m n =
      dispConj (((Real.sqrt η : ℝ) : ℂ) * β) (vacuumLossKernel η K) m n := by
  intro K
  have hK : ∀ a b, ‖K a b‖ ≤ ‖X‖ := by
    intro a b
    calc ‖K a b‖ ≤ ‖X (fockKet b)‖ := lp.norm_apply_le_norm (by norm_num) _ _
      _ ≤ ‖X‖ * ‖fockKet b‖ := X.le_opNorm _
      _ = ‖X‖ := by
        rw [fockKet, lp.norm_single (by norm_num), norm_one, mul_one]
  exact eq_18_of_bounded hη0 hη1 (norm_nonneg X) hK β
