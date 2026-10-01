-- Prove2me | solution 1 for MurtyKabadi.Reduction.problems8_9_equiv
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-01T08:33:19.684973+00:00
-- url     : https://prove2.me/submissions/9cfefa38-f6cb-4e73-9dae-116267e7cc26

import Theorems.Thm_MurtyKabadi_Reduction_problems6_7_equiv
import Theorems.Thm_MurtyKabadi_Reduction_problems7_8_equiv
import Definitions.Def_MurtyKabadi_Reduction_SubsetSum

open MurtyKabadi.Reduction

-- The coordinate estimate adapts the accepted Problems 6–7 proof,
-- submission 1af321f1-f9a9-4aeb-b834-414363594a93.
-- Its strengthened summation below works for f₂ < 1/2.

private lemma f2_eq_f4_on_P {n : ℕ} (hn : 0 < n) (d : Fin n → ℕ)
    (d0 δ : ℕ) (y s : Fin n → ℝ) (hp : (y, s) ∈ P n) :
    f2 d d0 δ y s = f4 d d0 δ y s := by
  have hsum : (∑ j, (y j + s j)) = (n : ℝ) := hp.2.2
  have hsq : (∑ j, (y j + s j - 1) ^ 2) =
      (∑ j, (y j + s j) ^ 2) - (n : ℝ) := by
    calc
      _ = ∑ j, ((y j + s j) ^ 2 - 2 * (y j + s j) + 1) := by
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = (∑ j, (y j + s j) ^ 2) - 2 * (∑ j, (y j + s j)) + (n : ℝ) := by
        simp [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
      _ = _ := by rw [hsum]; ring
  have hcorr : (∑ j, (d j : ℝ) * y j * (1 - y j)) =
      (∑ j, (d j : ℝ) * y j) - ∑ j, (d j : ℝ) * y j ^ 2 := by
    calc
      _ = ∑ j, ((d j : ℝ) * y j - (d j : ℝ) * y j ^ 2) := by
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = _ := by simp only [Finset.sum_sub_distrib]
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  unfold f2 f1 f4
  rw [hsq, hcorr, hsum]
  field_simp [hn0]
  ring

private theorem rounding_quadratic (A B ρ X : ℝ) (hA : 0 < A) (hρ : B ^ 2 ≤ 4 * A * ρ) :
    B * X - ρ ≤ A * X ^ 2 := by
  nlinarith [sq_nonneg (2 * A * X - B)]

/-- Per-coordinate estimate. -/
private theorem rounding_coordinate (y s d a δ ρ : ℝ) (hy : 0 ≤ y) (hs : 0 ≤ s) (hd : 0 ≤ d) (hda : d ≤ a)
    (hδa : 0 < δ - 2 * a) (hρ : (2 * a + d) ^ 2 ≤ 4 * (δ - 2 * a) * ρ) :
    d * |y - (if s < y then 1 else 0)| - ρ ≤
      δ * (y + s - 1) ^ 2 + y * s + 2 * a * (y * (1 - y)) := by
  have ha : 0 ≤ a := le_trans hd hda
  have hδ0 : 0 ≤ δ := by linarith
  have hρ0 : 0 ≤ ρ := by
    by_contra h
    push Not at h
    have : 4 * (δ - 2 * a) * ρ < 0 := by
      have := mul_pos (by norm_num : (0:ℝ) < 4) hδa
      nlinarith
    nlinarith [sq_nonneg (2 * a + d)]
  have hq : ∀ X : ℝ, (2 * a + d) * X - ρ ≤ (δ - 2 * a) * X ^ 2 :=
    fun X => rounding_quadratic _ _ _ X hδa hρ
  split_ifs with h
  · -- s < y
    have he : |y - 1| ≤ s + |y + s - 1| := by
      have : y - 1 = (y + s - 1) - s := by ring
      rw [this]
      calc |(y + s - 1) - s| ≤ |y + s - 1| + |s| := abs_sub _ _
        _ = s + |y + s - 1| := by rw [abs_of_nonneg hs]; ring
    have hQ : (δ - 2 * a) * (y + s - 1) ^ 2 + a * s - 2 * a * |y + s - 1|
        ≤ δ * (y + s - 1) ^ 2 + y * s + 2 * a * (y * (1 - y)) := by
      have h1 : 0 ≤ a * s * (y - s) := mul_nonneg (mul_nonneg ha hs) (by linarith)
      rcases le_or_gt 0 (y + s - 1) with hu | hu
      · rw [abs_of_nonneg hu]
        have h2 : 0 ≤ a * (y + s - 1) * s := mul_nonneg (mul_nonneg ha hu) hs
        nlinarith [mul_nonneg hy hs]
      · rw [abs_of_neg hu]
        have h2 : 0 ≤ a * (-(y + s - 1)) * (2 * y - s) :=
          mul_nonneg (mul_nonneg ha (by linarith)) (by linarith)
        nlinarith [mul_nonneg hy hs, mul_nonneg ha (sq_nonneg (y + s - 1)),
          mul_nonneg ha (by linarith : (0:ℝ) ≤ -(y + s - 1))]
    have h3 := hq |y + s - 1|
    have h4 : d * |y - 1| ≤ d * (s + |y + s - 1|) := mul_le_mul_of_nonneg_left he hd
    have h5 : d * s ≤ a * s := mul_le_mul_of_nonneg_right hda hs
    rw [sq_abs] at h3
    nlinarith
  · -- y ≤ s
    push Not at h
    rw [sub_zero, abs_of_nonneg hy]
    have h1 : 0 ≤ a * y * (s - y) := mul_nonneg (mul_nonneg ha hy) (by linarith)
    have h5 : d * y ≤ a * y := mul_le_mul_of_nonneg_right hda hy
    rcases le_or_gt (y + s - 1) 0 with hu | hu
    · have h2 : 0 ≤ a * y * (-(y + s - 1)) := mul_nonneg (mul_nonneg ha hy) (by linarith)
      nlinarith [mul_nonneg hy hs, mul_nonneg hδ0 (sq_nonneg (y + s - 1))]
    · have h2 : 0 ≤ a * (y + s - 1) * (s - y) := mul_nonneg (mul_nonneg ha hu.le) (by linarith)
      have h3 := hq (y + s - 1)
      nlinarith [mul_nonneg hy hs, mul_nonneg ha hu.le, mul_nonneg ha (sq_nonneg (y + s - 1)),
        mul_nonneg hd hu.le]

private theorem small_f2_rounds {n : ℕ} (d : Fin n → ℕ) (d0 δ : ℕ) (hd0 : 0 < d0)
    (hδ : 9 * (d0 * ∑ j, d j) ^ 2 + 2 * (d0 * ∑ j, d j) < δ)
    (y s : Fin n → ℝ) (hy : 0 ≤ y) (hs : 0 ≤ s) (hf : f2 d d0 δ y s < 1 / 2) :
    ∃ p ∈ P n, f1 d d0 δ p.1 p.2 ≤ 0 := by
  have hy' : ∀ j, 0 ≤ y j := fun j => hy j
  have hs' : ∀ j, 0 ≤ s j := fun j => hs j
  -- witness from a 0/1 vector
  have key : ∀ z : Fin n → ℝ, (∀ j, z j = 0 ∨ z j = 1) → ∑ j, (d j : ℝ) * z j = d0 →
      ∃ p ∈ P n, f1 d d0 δ p.1 p.2 ≤ 0 := by
    intro z hz hsum
    refine ⟨(z, fun j => 1 - z j), ⟨?_, ?_, ?_⟩, ?_⟩
    · intro j; rcases hz j with h | h <;> simp [h]
    · intro j; rcases hz j with h | h <;> simp [h]
    · simp
    · unfold f1
      have e1 : ∑ j, (z j + (1 - z j) - 1) ^ 2 = 0 := by simp
      have e2 : ∑ j, z j * (1 - z j) = 0 := by
        apply Finset.sum_eq_zero; intro j _; rcases hz j with h | h <;> simp [h]
      simp only at e1 e2 ⊢
      rw [hsum, e1, e2]; simp
  obtain ⟨Mr, hMr⟩ : ∃ Mr : ℝ, Mr = (d0 : ℝ) * ∑ j, (d j : ℝ) := ⟨_, rfl⟩
  have hMδ : 9 * Mr ^ 2 + 2 * Mr < δ := by
    rw [hMr]; exact_mod_cast hδ
  have hdj : ∀ j, (d j : ℝ) ≤ ∑ k, (d k : ℝ) := fun j =>
    Finset.single_le_sum (fun k _ => Nat.cast_nonneg (d k)) (Finset.mem_univ j)
  have hd0r : (1:ℝ) ≤ d0 := by exact_mod_cast hd0
  have hMr0 : 0 ≤ Mr := by rw [hMr]; positivity
  have hδM : 0 < (δ:ℝ) - 2 * Mr := by nlinarith
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = 9 * Mr / (4 * ((δ:ℝ) - 2 * Mr)) := ⟨_, rfl⟩
  have ht0 : 0 ≤ t := by rw [ht]; exact div_nonneg (by linarith) (by linarith)
  have htM : 4 * ((δ:ℝ) - 2 * Mr) * t = 9 * Mr := by
    rw [ht]; field_simp
  have htM' : t * Mr < 1 / 4 := by
    rw [ht, div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]; nlinarith
  let z : Fin n → ℝ := fun j => if s j < y j then 1 else 0
  have hcoord : ∀ j, (d j : ℝ) * |y j - z j| - t * (d0 * d j) ≤
      δ * (y j + s j - 1) ^ 2 + y j * s j + 2 * ((d0:ℝ) * d j) * (y j * (1 - y j)) := by
    intro j
    have hdj0 : (0:ℝ) ≤ d j := Nat.cast_nonneg _
    have haM : (d0:ℝ) * d j ≤ Mr := by
      rw [hMr]; exact mul_le_mul_of_nonneg_left (hdj j) (by positivity)
    have hdle : (d j : ℝ) ≤ d0 * d j := by nlinarith
    apply rounding_coordinate (y j) (s j) (d j) ((d0:ℝ) * d j) δ (t * (d0 * d j)) (hy' j) (hs' j)
      hdj0 hdle
    · linarith
    · have e1 : 4 * ((δ:ℝ) - 2 * Mr) * t * (d0 * d j) ≤
          4 * ((δ:ℝ) - 2 * (d0 * d j)) * (t * (d0 * d j)) := by
        have : 0 ≤ t * (d0 * d j) := by positivity
        nlinarith
      rw [htM] at e1
      nlinarith
  have hsumQ : ∑ j, ((d j : ℝ) * |y j - z j| - t * (d0 * d j)) ≤
      ∑ j, (δ * (y j + s j - 1) ^ 2 + y j * s j + 2 * ((d0:ℝ) * d j) * (y j * (1 - y j))) :=
    Finset.sum_le_sum (fun j _ => hcoord j)
  have hQeq : ∑ j, (δ * (y j + s j - 1) ^ 2 + y j * s j + 2 * ((d0:ℝ) * d j) * (y j * (1 - y j)))
      = (δ:ℝ) * ∑ j, (y j + s j - 1) ^ 2 + ∑ j, y j * s j
        + 2 * (d0:ℝ) * ∑ j, (d j : ℝ) * y j * (1 - y j) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro j _; ring
  have hLeq : ∑ j, ((d j : ℝ) * |y j - z j| - t * (d0 * d j))
      = ∑ j, (d j : ℝ) * |y j - z j| - t * Mr := by
    rw [Finset.sum_sub_distrib, hMr, Finset.mul_sum, Finset.mul_sum]
  have hf2eq : f2 d d0 δ y s = (∑ j, (d j : ℝ) * y j - d0) ^ 2 +
      ((δ:ℝ) * ∑ j, (y j + s j - 1) ^ 2 + ∑ j, y j * s j
        + 2 * (d0:ℝ) * ∑ j, (d j : ℝ) * y j * (1 - y j)) := by
    unfold f2 f1; ring
  obtain ⟨E, hE⟩ : ∃ E : ℝ, E = ∑ j, (d j : ℝ) * |y j - z j| := ⟨_, rfl⟩
  have hmain : (∑ j, (d j : ℝ) * y j - d0) ^ 2 + E - t * Mr < 1 / 2 := by
    rw [hE]; linarith
  have hW : |∑ j, (d j : ℝ) * (y j - z j)| ≤ E := by
    calc |∑ j, (d j : ℝ) * (y j - z j)| ≤ ∑ j, |(d j : ℝ) * (y j - z j)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ = E := by
        rw [hE]; apply Finset.sum_congr rfl; intro j _; rw [abs_mul, Nat.abs_cast]
  have hsplit : ∑ j, (d j : ℝ) * z j - d0
      = (∑ j, (d j : ℝ) * y j - d0) - ∑ j, (d j : ℝ) * (y j - z j) := by
    simp only [mul_sub, Finset.sum_sub_distrib]; ring
  have hround : |∑ j, (d j : ℝ) * z j - d0| ≤ |∑ j, (d j : ℝ) * y j - d0| + E := by
    rw [hsplit]
    calc |(∑ j, (d j : ℝ) * y j - d0) - ∑ j, (d j : ℝ) * (y j - z j)|
        ≤ |∑ j, (d j : ℝ) * y j - d0| + |∑ j, (d j : ℝ) * (y j - z j)| := abs_sub _ _
      _ ≤ |∑ j, (d j : ℝ) * y j - d0| + E := by linarith
  have hA : |∑ j, (d j : ℝ) * y j - d0| - (∑ j, (d j : ℝ) * y j - d0) ^ 2 ≤ 1 / 4 := by
    nlinarith [sq_abs (∑ j, (d j : ℝ) * y j - d0),
      sq_nonneg (|∑ j, (d j : ℝ) * y j - d0| - 1 / 2)]
  have hlt : |∑ j, (d j : ℝ) * z j - d0| < 1 := by linarith
  have hzcast : ((∑ j, d j * (if s j < y j then 1 else 0) : ℕ) : ℝ) = ∑ j, (d j : ℝ) * z j := by
    push_cast
    apply Finset.sum_congr rfl; intro j _
    simp only [z]
  obtain ⟨N, hN⟩ : ∃ N : ℕ, (N:ℝ) = ∑ j, (d j : ℝ) * z j := ⟨_, hzcast⟩
  rw [← hN] at hlt
  have hNd : N = d0 := by
    have h1 : |((N:ℤ) - (d0:ℤ) : ℤ)| < 1 := by
      have : |(((N:ℤ) - (d0:ℤ) : ℤ) : ℝ)| < 1 := by push_cast; exact hlt
      exact_mod_cast this
    have := Int.abs_lt_one_iff.mp h1
    omega
  apply key z (fun j => by simp only [z]; split_ifs <;> simp)
  rw [← hN, hNd]

private lemma one_coordinate_gap (a b : ℕ) (hb : 0 < b) (hab : a ≠ b)
    (y : ℝ) (hy : 0 ≤ y) (hy1 : y ≤ 1) :
    1 ≤ (b : ℝ) ^ 2 + y + ((a : ℝ) ^ 2 - 2 * b * a - 1) * y ^ 2 := by
  have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast hb
  have hb2 : (1 : ℝ) ≤ (b : ℝ) ^ 2 := by nlinarith
  have hdiff : (1 : ℝ) ≤ ((a : ℝ) - b) ^ 2 := by
    rcases lt_or_gt_of_ne hab with h | h
    · have h' : (a : ℝ) + 1 ≤ b := by exact_mod_cast h
      nlinarith
    · have h' : (b : ℝ) + 1 ≤ a := by exact_mod_cast h
      nlinarith
  by_cases hc : 0 ≤ (a : ℝ) ^ 2 - 2 * b * a - 1
  · nlinarith [mul_nonneg hc (sq_nonneg y)]
  · have hy2 : y ^ 2 ≤ y := by nlinarith
    have hprod := mul_le_mul_of_nonpos_left hy2 (le_of_not_ge hc)
    calc
      1 = (1 - y) * 1 + y * 1 := by ring
      _ ≤ (1 - y) * (b : ℝ) ^ 2 + y * ((a : ℝ) - b) ^ 2 :=
        add_le_add (mul_le_mul_of_nonneg_left hb2 (by linarith))
          (mul_le_mul_of_nonneg_left hdiff hy)
      _ = (b : ℝ) ^ 2 + y + ((a : ℝ) ^ 2 - 2 * b * a - 1) * y := by ring
      _ ≤ _ := by linarith

private lemma small_f2_one (d : Fin 1 → ℕ) (d0 δ : ℕ) (hd0 : 0 < d0)
    (y s : Fin 1 → ℝ) (hp : (y, s) ∈ P 1) (hf : f2 d d0 δ y s < 1 / 2) :
    ∃ p ∈ P 1, f1 d d0 δ p.1 p.2 ≤ 0 := by
  have hy : 0 ≤ y 0 := hp.1 0
  have hs : 0 ≤ s 0 := hp.2.1 0
  have hsum : y 0 + s 0 = 1 := by simpa using hp.2.2
  have heq : f2 d d0 δ y s =
      (d0 : ℝ) ^ 2 + y 0 + ((d 0 : ℝ) ^ 2 - 2 * d0 * d 0 - 1) * (y 0) ^ 2 := by
    have hs' : s 0 = 1 - y 0 := by linarith
    simp only [f2, f1, Fin.sum_univ_one, hs']
    ring
  have hd_eq : d 0 = d0 := by
    by_contra hne
    have hgap := one_coordinate_gap (d 0) d0 hd0 hne (y 0) hy (by linarith)
    rw [heq] at hf
    linarith
  refine ⟨((fun _ => 1), (fun _ => 0)), ⟨?_, ?_, ?_⟩, ?_⟩
  · intro j; norm_num
  · intro j; norm_num
  · simp
  · simp [f1, hd_eq]

private lemma f5_eq_f4_sub {n : ℕ} (hn : 0 < n) (d : Fin n → ℕ)
    (d0 δ : ℕ) (ε : ℚ) (p : (Fin n → ℝ) × (Fin n → ℝ)) (hp : p ∈ P n) :
    f5 d d0 δ ε p.1 p.2 = f4 d d0 δ p.1 p.2 - (ε : ℝ) := by
  have hn0 : (n : ℝ) ^ 2 ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr hn.ne')
  unfold f5
  rw [hp.2.2, div_mul_cancel₀ _ hn0]

theorem solution {n : ℕ} (hn : 0 < n) (d : Fin n → ℕ) (d0 δ : ℕ) (ε : ℚ)
    (hd : ∀ j, 0 < d j) (hd0 : 0 < d0)
    (hδ : 4 * (d0 * ∑ j, d j) ^ 2 * n ^ 3 < δ)
    (hε0 : 0 < ε) (hε : ε * (2 : ℚ) ^ (n * digitCount d d0 ^ 2) < 1) :
    (∃ p ∈ P n, f4 d d0 δ p.1 p.2 ≤ 0) ↔ ∃ p ∈ P n, f5 d d0 δ ε p.1 p.2 < 0 := by
  have hε0r : (0 : ℝ) < ε := by exact_mod_cast hε0
  have hdigits : 0 < (Nat.digits 10 d0).length := by
    rw [Nat.length_digits 10 d0 (by norm_num) hd0.ne']
    omega
  have hl : 0 < digitCount d d0 := by unfold digitCount; omega
  have hexp : 1 ≤ n * digitCount d d0 ^ 2 :=
    Nat.mul_pos hn (pow_pos hl _)
  have hpow : (2 : ℚ) ≤ 2 ^ (n * digitCount d d0 ^ 2) := by
    simpa using pow_le_pow_right₀ (by norm_num : (1 : ℚ) ≤ 2) hexp
  have hεtwiceq : 2 * ε < 1 := by
    nlinarith [mul_le_mul_of_nonneg_left hpow hε0.le]
  have hεtwice : (2 : ℝ) * ε < 1 := by exact_mod_cast hεtwiceq
  have hεhalf : (ε : ℝ) < 1 / 2 := by linarith
  constructor
  · rintro ⟨p, hp, hf⟩
    refine ⟨p, hp, ?_⟩
    rw [f5_eq_f4_sub hn d d0 δ ε p hp]
    linarith
  · rintro ⟨p, hp, hf⟩
    have hf2 : f2 d d0 δ p.1 p.2 < 1 / 2 := by
      rw [f5_eq_f4_sub hn d d0 δ ε p hp] at hf
      rw [f2_eq_f4_on_P hn d d0 δ p.1 p.2 hp]
      linarith
    have hf1 : ∃ q ∈ P n, f1 d d0 δ q.1 q.2 ≤ 0 := by
      by_cases hn1 : n = 1
      · subst n
        exact small_f2_one d d0 δ hd0 p.1 p.2 hp hf2
      · have hn2 : 2 ≤ n := by omega
        have hn3 : 8 ≤ n ^ 3 := by simpa using Nat.pow_le_pow_left hn2 3
        have hlarge : 32 * (d0 * ∑ j, d j) ^ 2 < δ :=
          lt_of_le_of_lt (by nlinarith) hδ
        have hstrong : 9 * (d0 * ∑ j, d j) ^ 2 + 2 * (d0 * ∑ j, d j) < δ := by
          have hMle : d0 * ∑ j, d j ≤ (d0 * ∑ j, d j) ^ 2 := by
            simpa [pow_two] using Nat.le_mul_self (d0 * ∑ j, d j)
          nlinarith
        exact small_f2_rounds d d0 δ hd0 hstrong p.1 p.2 hp.1 hp.2.1 hf2
    exact (problems7_8_equiv hn d d0 δ hd hd0 hδ).mp
      ((problems6_7_equiv d d0 δ hd hd0 hδ).mp hf1)
