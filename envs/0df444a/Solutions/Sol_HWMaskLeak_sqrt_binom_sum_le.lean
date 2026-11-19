-- Prove2me | solution 1 for HWMaskLeak.sqrt_binom_sum_le
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-18T07:36:34.623212+00:00
-- url     : https://prove2.me/submissions/6b2a910b-d449-4b47-9ba0-880862fe9224

import Mathlib

open Finset

lemma binom_var (n : ℕ) :
    ∑ w ∈ range (n + 1), (n.choose w : ℝ) * (2 * (w : ℝ) - n) ^ 2 = (n : ℝ) * 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h0 : ∑ w ∈ range (n + 1), (n.choose w : ℝ) = 2 ^ n := by
      exact_mod_cast Nat.sum_range_choose n
    set A : ℕ → ℝ := fun k => (n.choose k : ℝ) * (2 * (k : ℝ) - n + 1) ^ 2 with hA
    set B : ℕ → ℝ := fun j => (n.choose j : ℝ) * (2 * (j : ℝ) - n - 1) ^ 2 with hB
    rw [sum_range_succ']
    have hterm : ∀ k ∈ range (n + 1), ((n + 1).choose (k + 1) : ℝ) * (2 * ((k + 1 : ℕ) : ℝ) - ((n + 1 : ℕ) : ℝ)) ^ 2
        = A k + B (k + 1) := by
      intro k _
      rw [Nat.choose_succ_succ', hA, hB]; push_cast; ring
    rw [sum_congr rfl hterm, sum_add_distrib]
    -- Σ_{k<n+1} B (k+1) = Σ_{j<n+1} B j - B 0  (B (n+1) = 0)
    have hBshift : ∑ k ∈ range (n + 1), B (k + 1) = ∑ j ∈ range (n + 1), B j - B 0 := by
      have h1 := sum_range_succ' B (n + 1)
      have h2 : B (n + 1) = 0 := by simp [hB, Nat.choose_succ_self]
      rw [sum_range_succ, h2, add_zero] at h1
      linarith
    rw [hBshift]
    have hcomb : ∑ k ∈ range (n + 1), A k + ∑ j ∈ range (n + 1), B j =
        2 * ∑ w ∈ range (n + 1), (n.choose w : ℝ) * (2 * (w : ℝ) - n) ^ 2 +
          2 * ∑ w ∈ range (n + 1), (n.choose w : ℝ) := by
      rw [← sum_add_distrib, mul_sum, mul_sum, ← sum_add_distrib]
      apply sum_congr rfl; intro k _; simp only [hA, hB]; ring
    have hB0 : B 0 = (n + 1 : ℝ) ^ 2 := by simp [hB]; ring
    simp only [Nat.choose_zero_right, Nat.cast_one, one_mul, CharP.cast_eq_zero, mul_zero, zero_sub]
    push_cast
    rw [hB0, pow_succ]
    linear_combination hcomb + 2 * ih + 2 * h0

lemma lorentz_int (n : ℕ) (hn : 1 ≤ n) :
    ∫ x in (0:ℝ)..n, 1 / (1 + 4 * x ^ 2 / n) ≤ Real.pi * Real.sqrt n / 4 := by
  have hn0 : (0:ℝ) < n := by exact_mod_cast hn
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn0
  set c : ℝ := 2 / Real.sqrt n with hc
  have hc0 : 0 < c := by positivity
  have hfun : (fun x : ℝ => 1 / (1 + 4 * x ^ 2 / n)) = fun x => 1 / (1 + (c * x) ^ 2) := by
    funext x; congr 2; rw [hc, mul_pow, div_pow, Real.sq_sqrt hn0.le]; ring
  rw [hfun, intervalIntegral.integral_comp_mul_left (fun y => 1 / (1 + y ^ 2)) hc0.ne',
    integral_one_div_one_add_sq, mul_zero, Real.arctan_zero, sub_zero, smul_eq_mul]
  have hat := Real.arctan_lt_pi_div_two (c * n)
  rw [hc, inv_div]
  have : Real.sqrt n / 2 * Real.arctan (2 / Real.sqrt n * n) ≤ Real.sqrt n / 2 * (Real.pi / 2) :=
    mul_le_mul_of_nonneg_left (by rw [hc] at hat; linarith) (by positivity)
  linarith

lemma lorentz_sum (n : ℕ) (hn : 1 ≤ n) :
    ∑ w ∈ range (n + 1), 1 / (1 + 4 * ((w : ℝ) - n / 2) ^ 2 / n) ≤ 2 + Real.pi * Real.sqrt n / 2 := by
  have hn0 : (0:ℝ) < n := by exact_mod_cast hn
  set f : ℝ → ℝ := fun x => 1 / (1 + 4 * x ^ 2 / n) with hf
  have hfpos : ∀ x, 0 ≤ f x := fun x => by simp only [hf]; positivity
  have hf1 : ∀ x, f x ≤ 1 := fun x => by
    simp only [hf]; rw [div_le_one (by positivity)]; have : 0 ≤ 4 * x ^ 2 / n := by positivity
    linarith
  have hfanti : ∀ x y, 0 ≤ x → x ≤ y → f y ≤ f x := fun x y hx hxy => by
    simp only [hf]; apply one_div_le_one_div_of_le (by positivity)
    have : x ^ 2 ≤ y ^ 2 := by nlinarith
    have : 4 * x ^ 2 / n ≤ 4 * y ^ 2 / n := by apply div_le_div_of_nonneg_right _ hn0.le; linarith
    linarith
  have hfeven : ∀ x, f (-x) = f x := fun x => by simp [hf]
  set F : ℕ → ℝ := fun w => f ((w : ℝ) - n / 2) with hF
  change ∑ w ∈ range (n + 1), F w ≤ _
  set R := (range (n + 1)).filter (fun w => n ≤ 2 * w) with hR
  set L := (range (n + 1)).filter (fun w => ¬ n ≤ 2 * w) with hL
  have hsplit : ∑ w ∈ range (n + 1), F w = ∑ w ∈ R, F w + ∑ w ∈ L, F w :=
    (sum_filter_add_sum_filter_not _ _ _).symm
  -- reflect L into R
  have hLR : ∑ w ∈ L, F w ≤ ∑ w ∈ R, F w := by
    have hrefl : ∀ w ∈ L, F w = F (n - w) := by
      intro w hw
      have hwn : w ≤ n := by simp [hL] at hw; omega
      simp only [hF]; rw [← hfeven]; congr 1; push_cast [hwn]; ring
    rw [sum_congr rfl hrefl]
    rw [← sum_image (s := L) (g := fun w => n - w) (f := F) (by
      intro a ha b hb hab; simp [hL] at ha hb; simp at hab; omega)]
    apply sum_le_sum_of_subset_of_nonneg
    · intro x hx; simp only [mem_image, hL, mem_filter, mem_range] at hx
      obtain ⟨w, ⟨hw1, hw2⟩, rfl⟩ := hx
      simp only [hR, mem_filter, mem_range]; omega
    · intro i _ _; exact hfpos _
  -- bound R by Σ_{i ≤ n} f i
  set m := (n + 1) / 2 with hm
  have hRbound : ∑ w ∈ R, F w ≤ ∑ i ∈ range (n + 1), f i := by
    have hle : ∀ w ∈ R, F w ≤ f ((w - m : ℕ) : ℝ) := by
      intro w hw
      simp only [hR, mem_filter, mem_range] at hw
      apply hfanti _ _ (by positivity)
      have hmw : m ≤ w := by omega
      have : (m : ℝ) ≥ n / 2 := by
        have : n ≤ 2 * m := by omega
        have : (n : ℝ) ≤ 2 * m := by exact_mod_cast this
        linarith
      push_cast [hmw]; linarith
    refine (sum_le_sum hle).trans ?_
    rw [← sum_image (s := R) (g := fun w : ℕ => w - m) (f := fun i : ℕ => f (i : ℝ)) (by
      intro a ha b hb hab; simp [hR] at ha hb; simp at hab; omega)]
    apply sum_le_sum_of_subset_of_nonneg
    · intro x hx; simp only [mem_image, hR, mem_filter, mem_range] at hx
      obtain ⟨w, ⟨hw1, hw2⟩, rfl⟩ := hx
      simp only [mem_range]; omega
    · intro i _ _; exact hfpos _
  have hsum_int : ∑ i ∈ range (n + 1), f i ≤ 1 + Real.pi * Real.sqrt n / 4 := by
    rw [sum_range_succ']
    have hanti : AntitoneOn f (Set.Icc 0 (0 + (n : ℝ))) := by
      intro x hx y hy hxy; exact hfanti x y hx.1 hxy
    have h1 := hanti.sum_le_integral
    simp only [zero_add, Nat.cast_add, Nat.cast_one] at h1
    have h2 : ∫ x in (0:ℝ)..n, f x ≤ Real.pi * Real.sqrt n / 4 := lorentz_int n hn
    have h0 : f ((0 : ℕ) : ℝ) ≤ 1 := hf1 _
    have : ∑ i ∈ range n, f ((i + 1 : ℕ) : ℝ) = ∑ i ∈ range n, f ((i : ℝ) + 1) := by
      apply sum_congr rfl; intro i _; push_cast; rfl
    rw [this]
    calc ∑ i ∈ range n, f ((i : ℝ) + 1) + f ((0 : ℕ) : ℝ) ≤ (∫ x in (0:ℝ)..n, f x) + 1 :=
          add_le_add (by convert h1 using 2) h0
      _ ≤ _ := by linarith
  linarith

theorem solution (n : ℕ) (hn : 1 ≤ n) :
    ∑ w ∈ Finset.range (n + 1), Real.sqrt ((n.choose w : ℝ) * ((2 : ℝ) ^ n)⁻¹) ≤
      Real.sqrt 5 + Real.sqrt (5 * Real.pi / 2) * (n : ℝ) ^ ((1 : ℝ) / 4) := by
  have hn0 : (0:ℝ) < n := by exact_mod_cast hn
  have h2n : (0:ℝ) < 2 ^ n := by positivity
  set b : ℕ → ℝ := fun w => (n.choose w : ℝ) * ((2 : ℝ) ^ n)⁻¹ with hb
  set g : ℕ → ℝ := fun w => 1 + 4 * ((w : ℝ) - n / 2) ^ 2 / n with hg
  have hb0 : ∀ w, 0 ≤ b w := fun w => by simp only [hb]; positivity
  have hg0 : ∀ w, 0 < g w := fun w => by simp only [hg]; positivity
  -- Cauchy-Schwarz
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range (n + 1))
    (fun w => Real.sqrt (b w * g w)) (fun w => Real.sqrt (1 / g w))
  have hprod : ∀ w, Real.sqrt (b w * g w) * Real.sqrt (1 / g w) = Real.sqrt (b w) := by
    intro w
    rw [← Real.sqrt_mul (mul_nonneg (hb0 w) (hg0 w).le)]
    congr 1; field_simp [(hg0 w).ne']
  simp only [hprod, Real.sq_sqrt (mul_nonneg (hb0 _) (hg0 _).le),
    Real.sq_sqrt (one_div_nonneg.mpr (hg0 _).le)] at hCS
  have hbg : ∑ w ∈ Finset.range (n + 1), b w * g w = 2 := by
    have hsumb : ∑ w ∈ Finset.range (n + 1), b w = 1 := by
      simp only [hb]; rw [← Finset.sum_mul]
      have : ∑ w ∈ Finset.range (n + 1), (n.choose w : ℝ) = 2 ^ n := by
        exact_mod_cast Nat.sum_range_choose n
      rw [this, mul_inv_cancel₀ h2n.ne']
    have hvar := binom_var n
    have e : ∀ w ∈ Finset.range (n + 1), b w * g w =
        b w + ((n.choose w : ℝ) * (2 * (w : ℝ) - n) ^ 2) * ((2 : ℝ) ^ n)⁻¹ / n := by
      intro w _; simp only [hb, hg]; field_simp; ring
    rw [Finset.sum_congr rfl e, Finset.sum_add_distrib, hsumb, ← Finset.sum_div, ← Finset.sum_mul,
      hvar]
    field_simp; ring
  have hlor : ∑ w ∈ Finset.range (n + 1), 1 / g w ≤ 2 + Real.pi * Real.sqrt n / 2 := lorentz_sum n hn
  rw [hbg] at hCS
  have hsq : (∑ w ∈ Finset.range (n + 1), Real.sqrt (b w)) ^ 2 ≤ 4 + Real.pi * Real.sqrt n := by
    nlinarith [hCS, hlor]
  have hS0 : 0 ≤ ∑ w ∈ Finset.range (n + 1), Real.sqrt (b w) :=
    Finset.sum_nonneg (fun w _ => Real.sqrt_nonneg _)
  set q := (n : ℝ) ^ ((1 : ℝ) / 4) with hq
  have hq0 : 0 ≤ q := by positivity
  have hq2 : q ^ 2 = Real.sqrt n := by
    rw [hq, ← Real.rpow_natCast, ← Real.rpow_mul hn0.le, Real.sqrt_eq_rpow]; norm_num
  have hY0 : 0 ≤ Real.sqrt 5 + Real.sqrt (5 * Real.pi / 2) * q := by positivity
  have hY2 : 4 + Real.pi * Real.sqrt n ≤ (Real.sqrt 5 + Real.sqrt (5 * Real.pi / 2) * q) ^ 2 := by
    have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
    have hp : Real.sqrt (5 * Real.pi / 2) ^ 2 = 5 * Real.pi / 2 := Real.sq_sqrt (by positivity)
    have hsn : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
    have hcross : 0 ≤ Real.sqrt 5 * Real.sqrt (5 * Real.pi / 2) * q := by positivity
    have hpi : 0 < Real.pi := Real.pi_pos
    nlinarith [hq2]
  show ∑ w ∈ Finset.range (n + 1), Real.sqrt (b w) ≤ _
  exact (pow_le_pow_iff_left₀ hS0 hY0 (by norm_num : (2:ℕ) ≠ 0)).mp (hsq.trans hY2)
