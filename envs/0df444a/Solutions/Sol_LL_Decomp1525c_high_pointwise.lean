-- Prove2me | solution 1 for LL_Decomp1525c.high_pointwise
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T17:18:09.435481+00:00
-- url     : https://prove2.me/submissions/c5cc1bf8-7101-40d7-ae66-5ed74b2e9cec

import Mathlib
import Definitions.Def_LL_Decomp1525c_P1V
import Definitions.Def_LL_Decomp1525c_thetaI

open Finset

namespace S218LL

/-- θ splits at a lower threshold `m ≤ y`. -/
lemma theta_split (y m : ℝ) (hm0 : 0 ≤ m) (hmy : m ≤ y) :
    Chebyshev.theta y = Chebyshev.theta m +
      ∑ p ∈ ((Ioc 0 ⌊y⌋₊).filter Nat.Prime).filter (fun p => ¬ p ≤ ⌊m⌋₊), Real.log p := by
  rw [Chebyshev.theta, Chebyshev.theta, ← sum_filter_add_sum_filter_not _ (fun p => p ≤ ⌊m⌋₊)]
  congr 1
  apply sum_congr _ (fun _ _ => rfl)
  ext p
  have := Nat.floor_le_floor (a := m) (b := y) hmy
  simp only [mem_filter, mem_Ioc]
  constructor
  · rintro ⟨⟨⟨h1, _⟩, h3⟩, h4⟩; exact ⟨⟨h1, h4⟩, h3⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨⟨h1, le_trans h2 this⟩, h3⟩, h2⟩

lemma theta_two : Chebyshev.theta 2 = Real.log 2 := by
  rw [Chebyshev.theta, show ⌊(2:ℝ)⌋₊ = 2 by norm_num,
    show (Ioc 0 2).filter Nat.Prime = {2} by decide]
  simp

lemma thetaI_low_eq (x u : ℝ) (hx : 6 ≤ x) (hu3 : 3 ≤ u) (hux : u ≤ x) :
    LL_Decomp1525c.thetaI x u = Chebyshev.theta (x - 3) - Chebyshev.theta (max (x - u) 2) := by
  set m := max (x - u) 2 with hm
  have hm0 : 0 ≤ m := le_trans (by norm_num) (le_max_right _ _)
  have hmy : m ≤ x - 3 := max_le (by linarith) (by linarith)
  rw [theta_split (x - 3) m hm0 hmy, add_sub_cancel_left, LL_Decomp1525c.thetaI,
    LL_Decomp1525c.P1V]
  apply sum_congr _ (fun _ _ => rfl)
  ext p
  have hx3 : (0:ℝ) ≤ x - 3 := by linarith
  simp only [mem_filter, mem_Icc, mem_Ioc, not_le]
  rw [Nat.floor_lt hm0]
  constructor
  · rintro ⟨⟨⟨h1, h2⟩, hp⟩, h3, h4⟩
    refine ⟨⟨⟨by omega, h2⟩, hp⟩, max_lt (by linarith) ?_⟩
    exact_mod_cast (show 2 < p by omega)
  · rintro ⟨⟨⟨h1, h2⟩, hp⟩, h3⟩
    have hp2 : (2:ℝ) < p := lt_of_le_of_lt (le_max_right _ _) h3
    have hp3 : 3 ≤ p := by exact_mod_cast (show (2:ℝ) < p from hp2)
    have hpx : (p:ℝ) ≤ x - 3 := (Nat.le_floor_iff hx3).1 h2
    exact ⟨⟨⟨hp3, h2⟩, hp⟩, by linarith [le_max_left (x - u) 2], by linarith⟩

lemma theta_err (h215 : ∀ y : ℝ, 678407 ≤ y → |Chebyshev.theta y - y| < y / (40 * Real.log y))
    (m : ℝ) (hm2 : 2 ≤ m) :
    |Chebyshev.theta m - m| ≤ m / (40 * Real.log m) + 678407 := by
  have hlog : 0 < Real.log m := Real.log_pos (by linarith)
  have hq : 0 ≤ m / (40 * Real.log m) := by positivity
  rcases le_or_gt 678407 m with h | h
  · linarith [h215 m h]
  · have h4 : Real.log 4 < 2 := by
      have : Real.log 4 = 2 * Real.log 2 := by
        rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
      rw [this]; linarith [Real.log_two_lt_d9]
    have hup := Chebyshev.theta_le_log4_mul_x (x := m) (by linarith)
    have hnn := Chebyshev.theta_nonneg m
    rw [abs_le]
    constructor <;> nlinarith

lemma div_log_mono {x : ℝ} (hx : 10 ^ 52 ≤ x) :
    (x - 3) / (40 * Real.log (x - 3)) ≤ x / (40 * Real.log x) := by
  have hx3 : 0 < x - 3 := by linarith
  have hl3 : 0 < Real.log (x - 3) := Real.log_pos (by linarith)
  have hlx : 2 ≤ Real.log x := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have : Real.exp 2 < 8 := by
      have := Real.exp_one_lt_d9
      calc Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
        _ < 8 := by nlinarith [Real.exp_pos 1]
    linarith
  have hdiff : Real.log x - Real.log (x - 3) ≤ 3 / (x - 3) := by
    rw [← Real.log_div (by linarith) hx3.ne']
    have := Real.log_le_sub_one_of_pos (x := x / (x - 3)) (by positivity)
    have he : x / (x - 3) - 1 = 3 / (x - 3) := by field_simp; ring
    linarith
  have h3 : 3 / (x - 3) * x ≤ 6 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hx3]; nlinarith
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have : (x - 3) * Real.log x ≤ x * Real.log (x - 3) := by
    have : x * (Real.log x - Real.log (x - 3)) ≤ 6 := by
      calc x * (Real.log x - Real.log (x - 3)) ≤ x * (3 / (x - 3)) :=
            mul_le_mul_of_nonneg_left hdiff (by linarith)
        _ ≤ 6 := by linarith [h3]
    nlinarith
  nlinarith

end S218LL

theorem solution
    (h215 : ∀ y : ℝ, 678407 ≤ y → |Chebyshev.theta y - y| < y / (40 * Real.log y))
    (x u : ℝ) (hx : 10 ^ 52 ≤ x) (hxu : x ≤ u) (hu : u ≤ 2 * x) :
    |LL_Decomp1525c.thetaI x u - (2 * x - u)| ≤
      max (min (x - 3) (2 * x - u)) 2 / (40 * Real.log (max (min (x - 3) (2 * x - u)) 2))
        + 678412 := by
  set k := min (x - 3) (2 * x - u) with hk
  have hthI : LL_Decomp1525c.thetaI x u = max (Chebyshev.theta k - Real.log 2) 0 := by
    have hk0 : 0 ≤ k := le_min (by linarith) (by linarith)
    rcases lt_or_ge k 2 with h2 | h2
    · have hle : Chebyshev.theta k ≤ Real.log 2 :=
        S218LL.theta_two ▸ Chebyshev.theta_mono h2.le
      rw [max_eq_right (by linarith), LL_Decomp1525c.thetaI]
      apply sum_eq_zero
      intro p hp
      exfalso
      simp only [LL_Decomp1525c.P1V, mem_filter, mem_Icc] at hp
      have hx3 : (0:ℝ) ≤ x - 3 := by linarith
      have hpx : (p:ℝ) ≤ x - 3 := (Nat.le_floor_iff hx3).1 hp.1.1.2
      have hp3 : (3:ℝ) ≤ p := by exact_mod_cast hp.1.1.1
      have : (p:ℝ) ≤ k := le_min hpx (by linarith [hp.2.2])
      linarith
    · rw [S218LL.theta_split k 2 (by norm_num) h2, S218LL.theta_two, add_sub_cancel_left,
        max_eq_left (sum_nonneg fun p _ => Real.log_natCast_nonneg p), LL_Decomp1525c.thetaI,
        LL_Decomp1525c.P1V]
      apply sum_congr _ (fun _ _ => rfl)
      ext p
      have hx3 : (0:ℝ) ≤ x - 3 := by linarith
      simp only [mem_filter, mem_Icc, mem_Ioc, not_le, show ⌊(2:ℝ)⌋₊ = 2 by norm_num]
      constructor
      · rintro ⟨⟨⟨h1, h2⟩, hp⟩, h3, h4⟩
        have hpx : (p:ℝ) ≤ x - 3 := (Nat.le_floor_iff hx3).1 h2
        refine ⟨⟨⟨by omega, (Nat.le_floor_iff hk0).2 (le_min hpx (by linarith))⟩, hp⟩, by omega⟩
      · rintro ⟨⟨⟨h1, h2⟩, hp⟩, h3⟩
        have hpk : (p:ℝ) ≤ k := (Nat.le_floor_iff hk0).1 h2
        have hp3 : (3:ℝ) ≤ p := by exact_mod_cast h3
        refine ⟨⟨⟨h3, (Nat.le_floor_iff hx3).2 (le_trans hpk (min_le_left _ _))⟩, hp⟩, by linarith, ?_⟩
        linarith [min_le_right (x - 3) (2 * x - u)]
  rw [hthI]
  have hk1 : k ≤ 2 * x - u := min_le_right _ _
  have hk2 : 2 * x - u - 3 ≤ k := le_min (by linarith) (by linarith)
  have hl2 : Real.log 2 < 1 := by linarith [Real.log_two_lt_d9]
  have hl2' : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rcases lt_or_ge k 2 with h2 | h2
  · have hle : Chebyshev.theta k ≤ Real.log 2 :=
      S218LL.theta_two ▸ Chebyshev.theta_mono h2.le
    have hkx : k = 2 * x - u := by
      rcases min_choice (x - 3) (2 * x - u) with h | h
      · rw [hk, h] at h2; linarith
      · rw [hk, h]
    rw [max_eq_right (by linarith), max_eq_right h2.le]
    have : 0 ≤ (2:ℝ) / (40 * Real.log 2) := by positivity
    rw [abs_le]; constructor <;> linarith
  · have hge : Real.log 2 ≤ Chebyshev.theta k :=
      S218LL.theta_two ▸ Chebyshev.theta_mono h2
    rw [max_eq_left (by linarith), max_eq_left h2]
    have e := abs_le.1 (S218LL.theta_err h215 k h2)
    rw [abs_le]; constructor <;> linarith
