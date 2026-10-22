-- Prove2me | solution 1 for IQCAlg.HeavyBall.iterates_4_to_11
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T07:29:20.741981+00:00
-- url     : https://prove2.me/submissions/cb436cf4-5bc1-4c6b-9907-cc376a496da2

import Mathlib
import Definitions.Def_IQCAlg_HeavyBall_Setting

set_option autoImplicit false

open IQCAlg.HeavyBall

namespace IQHAux

lemma gradF_lt {x : ℝ} (h : x < 1) : gradF x = 25 * x := by simp [gradF, h]

lemma gradF_mid {x : ℝ} (h1 : 1 ≤ x) (h2 : x < 2) : gradF x = x + 24 := by
  simp [gradF, not_lt.2 h1, h2]

lemma gradF_ge {x : ℝ} (h : 2 ≤ x) : gradF x = 25 * x - 24 := by
  have h1 : ¬ x < 1 := by intro h'; linarith
  have h2 : ¬ x < 2 := by intro h'; linarith
  simp [gradF, h1, h2]

lemma cyc0 {k : ℕ} (h : k % 3 = 0) : cyc k = pC := by simp [cyc, h]
lemma cyc1 {k : ℕ} (h : k % 3 = 1) : cyc k = qC := by simp [cyc, h]
lemma cyc2 {k : ℕ} (h : k % 3 = 2) : cyc k = rC := by simp [cyc, h]

lemma p_lt : pC < 1 := by unfold pC; norm_num
lemma q_lt : qC < 1 := by unfold qC; norm_num
lemma r_gt : 2 < rC := by unfold rC; norm_num

lemma cyc_cases (k : ℕ) : cyc k = pC ∨ cyc k = qC ∨ cyc k = rC := by
  have : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  rcases this with h | h | h
  · exact Or.inl (cyc0 h)
  · exact Or.inr (Or.inl (cyc1 h))
  · exact Or.inr (Or.inr (cyc2 h))

lemma cyc_B1 : IsB1Traj cyc := by
  intro k
  have : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  rcases this with h | h | h
  · rw [cyc2 (by omega), cyc1 (by omega), cyc0 h, gradF_lt q_lt]
    unfold pC qC rC; norm_num
  · rw [cyc0 (by omega), cyc2 (by omega), cyc1 h, gradF_ge r_gt.le]
    unfold pC qC rC; norm_num
  · rw [cyc1 (by omega), cyc0 (by omega), cyc2 h, gradF_lt p_lt]
    unfold pC qC rC; norm_num

lemma eps_rec (x : ℕ → ℝ) (hx : IsB1Traj x) (k : ℕ)
    (hpiece : (cyc (k + 1) < 1 → x (k + 1) < 1) ∧ (2 < cyc (k + 1) → 2 < x (k + 1))) :
    eps x (k + 2) = -4 / 3 * eps x (k + 1) - 4 / 9 * eps x k := by
  have h1 := hx k
  have h2 := cyc_B1 k
  unfold eps
  rcases cyc_cases (k + 1) with h | h | h
  · have hc : cyc (k + 1) < 1 := by rw [h]; exact p_lt
    have hxk := hpiece.1 hc
    rw [gradF_lt hxk] at h1
    rw [gradF_lt hc] at h2
    linarith
  · have hc : cyc (k + 1) < 1 := by rw [h]; exact q_lt
    have hxk := hpiece.1 hc
    rw [gradF_lt hxk] at h1
    rw [gradF_lt hc] at h2
    linarith
  · have hc : 2 < cyc (k + 1) := by rw [h]; exact r_gt
    have hxk := hpiece.2 hc
    rw [gradF_ge hxk.le] at h1
    rw [gradF_ge hc.le] at h2
    linarith

lemma sqrt25 : Real.sqrt 25 = 5 := by
  rw [show (25:ℝ) = 5 ^ 2 by norm_num]; exact Real.sqrt_sq (by norm_num)

lemma hbAlpha_25 : hbAlpha 25 1 = 1 / 9 := by
  unfold hbAlpha; rw [sqrt25, Real.sqrt_one]; norm_num

lemma hbBeta_25 : hbBeta 25 1 = 4 / 9 := by
  unfold hbBeta kappa; rw [div_one, sqrt25]; norm_num

lemma eps_chain (x : ℕ → ℝ) (hx : IsB1Traj x) (k : ℕ)
    (hp : ∀ j : ℕ, 1 ≤ j → j ≤ 7 →
      (cyc (k + j) < 1 → x (k + j) < 1) ∧ (2 < cyc (k + j) → 2 < x (k + j))) :
    eps x (k + 8) = (-1024 / 2187) * eps x (k + 1) + (-1792 / 6561) * eps x k := by
  have r0 := eps_rec x hx k (hp 1 (by norm_num) (by norm_num))
  have r1 := eps_rec x hx (k + 1) (hp 2 (by norm_num) (by norm_num))
  have r2 := eps_rec x hx (k + 2) (hp 3 (by norm_num) (by norm_num))
  have r3 := eps_rec x hx (k + 3) (hp 4 (by norm_num) (by norm_num))
  have r4 := eps_rec x hx (k + 4) (hp 5 (by norm_num) (by norm_num))
  have r5 := eps_rec x hx (k + 5) (hp 6 (by norm_num) (by norm_num))
  have r6 := eps_rec x hx (k + 6) (hp 7 (by norm_num) (by norm_num))
  have e : ∀ m : ℕ, k + m + 2 = k + (m + 2) := fun m => by omega
  simp only [e] at r1 r2 r3 r4 r5 r6
  norm_num at r1 r2 r3 r4 r5 r6
  linarith

lemma eps8_sq (x : ℕ → ℝ) (hx : IsB1Traj x) (k : ℕ)
    (hp : ∀ j : ℕ, 1 ≤ j → j ≤ 7 →
      (cyc (k + j) < 1 → x (k + j) < 1) ∧ (2 < cyc (k + j) → 2 < x (k + j))) :
    eps x (k + 8) ^ 2 ≤ 3 / 10 * (eps x (k + 1) ^ 2 + eps x k ^ 2) := by
  rw [eps_chain x hx k hp]
  nlinarith [sq_nonneg ((-1792 / 6561) * eps x (k + 1) - (-1024 / 2187) * eps x k),
    sq_nonneg (eps x (k + 1)), sq_nonneg (eps x k)]

end IQHAux

open IQHAux

theorem solution :
    ∀ j : ℕ, 4 ≤ j → j ≤ 11 →
      |hbRun gradF (hbAlpha 25 1) (hbBeta 25 1) (33 / 10) j - cyc j| < epsBar := by
  rw [hbAlpha_25, hbBeta_25]
  have hstep : ∀ k : ℕ, hbRun gradF (1 / 9) (4 / 9) (33 / 10) (k + 2) =
      hbRun gradF (1 / 9) (4 / 9) (33 / 10) (k + 1) - 1 / 9 * gradF (hbRun gradF (1 / 9) (4 / 9) (33 / 10) (k + 1))
        + 4 / 9 * (hbRun gradF (1 / 9) (4 / 9) (33 / 10) (k + 1) - hbRun gradF (1 / 9) (4 / 9) (33 / 10) k) := fun k => by
    simp only [hbRun]
  have e0 : hbRun gradF (1 / 9) (4 / 9) (33 / 10) 0 = (33 / 10 : ℝ) := by simp only [hbRun]
  have e1 : hbRun gradF (1 / 9) (4 / 9) (33 / 10) 1 = (-16 / 5 : ℝ) := by
    simp only [hbRun]
    rw [gradF_ge (by norm_num)]
    norm_num
  have s2 : hbRun gradF (1 / 9) (4 / 9) (33 / 10) 2 = hbRun gradF (1 / 9) (4 / 9) (33 / 10) 1 - 1 / 9 * gradF (hbRun gradF (1 / 9) (4 / 9) (33 / 10) 1) + 4 / 9 * (hbRun gradF (1 / 9) (4 / 9) (33 / 10) 1 - hbRun gradF (1 / 9) (4 / 9) (33 / 10) 0) := hstep 0
  have e2 : hbRun gradF (1 / 9) (4 / 9) (33 / 10) 2 = (14 / 5 : ℝ) := by
    rw [s2, e1, e0, gradF_lt (by norm_num)]
    norm_num
  have s3 : hbRun gradF (1 / 9) (4 / 9) (33 / 10) 3 = hbRun gradF (1 / 9) (4 / 9) (33 / 10) 2 - 1 / 9 * gradF (hbRun gradF (1 / 9) (4 / 9) (33 / 10) 2) + 4 / 9 * (hbRun gradF (1 / 9) (4 / 9) (33 / 10) 2 - hbRun gradF (1 / 9) (4 / 9) (33 / 10) 1) := hstep 1
  have e3 : hbRun gradF (1 / 9) (4 / 9) (33 / 10) 3 = (16 / 45 : ℝ) := by
    rw [s3, e2, e1, gradF_ge (by norm_num)]
    norm_num
  have s4 : hbRun gradF (1 / 9) (4 / 9) (33 / 10) 4 = hbRun gradF (1 / 9) (4 / 9) (33 / 10) 3 - 1 / 9 * gradF (hbRun gradF (1 / 9) (4 / 9) (33 / 10) 3) + 4 / 9 * (hbRun gradF (1 / 9) (4 / 9) (33 / 10) 3 - hbRun gradF (1 / 9) (4 / 9) (33 / 10) 2) := hstep 2
  have e4 : hbRun gradF (1 / 9) (4 / 9) (33 / 10) 4 = (-232 / 135 : ℝ) := by
    rw [s4, e3, e2, gradF_lt (by norm_num)]
    norm_num
  have s5 : hbRun gradF (1 / 9) (4 / 9) (33 / 10) 5 = hbRun gradF (1 / 9) (4 / 9) (33 / 10) 4 - 1 / 9 * gradF (hbRun gradF (1 / 9) (4 / 9) (33 / 10) 4) + 4 / 9 * (hbRun gradF (1 / 9) (4 / 9) (33 / 10) 4 - hbRun gradF (1 / 9) (4 / 9) (33 / 10) 3) := hstep 3
  have e5 : hbRun gradF (1 / 9) (4 / 9) (33 / 10) 5 = (32 / 15 : ℝ) := by
    rw [s5, e4, e3, gradF_lt (by norm_num)]
    norm_num
  have s6 : hbRun gradF (1 / 9) (4 / 9) (33 / 10) 6 = hbRun gradF (1 / 9) (4 / 9) (33 / 10) 5 - 1 / 9 * gradF (hbRun gradF (1 / 9) (4 / 9) (33 / 10) 5) + 4 / 9 * (hbRun gradF (1 / 9) (4 / 9) (33 / 10) 5 - hbRun gradF (1 / 9) (4 / 9) (33 / 10) 4) := hstep 4
  have e6 : hbRun gradF (1 / 9) (4 / 9) (33 / 10) 6 = (712 / 1215 : ℝ) := by
    rw [s6, e5, e4, gradF_ge (by norm_num)]
    norm_num
  have s7 : hbRun gradF (1 / 9) (4 / 9) (33 / 10) 7 = hbRun gradF (1 / 9) (4 / 9) (33 / 10) 6 - 1 / 9 * gradF (hbRun gradF (1 / 9) (4 / 9) (33 / 10) 6) + 4 / 9 * (hbRun gradF (1 / 9) (4 / 9) (33 / 10) 6 - hbRun gradF (1 / 9) (4 / 9) (33 / 10) 5) := hstep 5
  have e7 : hbRun gradF (1 / 9) (4 / 9) (33 / 10) 7 = (-6304 / 3645 : ℝ) := by
    rw [s7, e6, e5, gradF_lt (by norm_num)]
    norm_num
  have s8 : hbRun gradF (1 / 9) (4 / 9) (33 / 10) 8 = hbRun gradF (1 / 9) (4 / 9) (33 / 10) 7 - 1 / 9 * gradF (hbRun gradF (1 / 9) (4 / 9) (33 / 10) 7) + 4 / 9 * (hbRun gradF (1 / 9) (4 / 9) (33 / 10) 7 - hbRun gradF (1 / 9) (4 / 9) (33 / 10) 6) := hstep 6
  have e8 : hbRun gradF (1 / 9) (4 / 9) (33 / 10) 8 = (7456 / 3645 : ℝ) := by
    rw [s8, e7, e6, gradF_lt (by norm_num)]
    norm_num
  have s9 : hbRun gradF (1 / 9) (4 / 9) (33 / 10) 9 = hbRun gradF (1 / 9) (4 / 9) (33 / 10) 8 - 1 / 9 * gradF (hbRun gradF (1 / 9) (4 / 9) (33 / 10) 8) + 4 / 9 * (hbRun gradF (1 / 9) (4 / 9) (33 / 10) 8 - hbRun gradF (1 / 9) (4 / 9) (33 / 10) 7) := hstep 7
  have e9 : hbRun gradF (1 / 9) (4 / 9) (33 / 10) 9 = (23224 / 32805 : ℝ) := by
    rw [s9, e8, e7, gradF_ge (by norm_num)]
    norm_num
  have s10 : hbRun gradF (1 / 9) (4 / 9) (33 / 10) 10 = hbRun gradF (1 / 9) (4 / 9) (33 / 10) 9 - 1 / 9 * gradF (hbRun gradF (1 / 9) (4 / 9) (33 / 10) 9) + 4 / 9 * (hbRun gradF (1 / 9) (4 / 9) (33 / 10) 9 - hbRun gradF (1 / 9) (4 / 9) (33 / 10) 8) := hstep 8
  have e10 : hbRun gradF (1 / 9) (4 / 9) (33 / 10) 10 = (-182368 / 98415 : ℝ) := by
    rw [s10, e9, e8, gradF_lt (by norm_num)]
    norm_num
  have s11 : hbRun gradF (1 / 9) (4 / 9) (33 / 10) 11 = hbRun gradF (1 / 9) (4 / 9) (33 / 10) 10 - 1 / 9 * gradF (hbRun gradF (1 / 9) (4 / 9) (33 / 10) 10) + 4 / 9 * (hbRun gradF (1 / 9) (4 / 9) (33 / 10) 10 - hbRun gradF (1 / 9) (4 / 9) (33 / 10) 9) := hstep 9
  have e11 : hbRun gradF (1 / 9) (4 / 9) (33 / 10) 11 = (212192 / 98415 : ℝ) := by
    rw [s11, e10, e9, gradF_lt (by norm_num)]
    norm_num
  intro j h1 h2
  interval_cases j
  · rw [e4, cyc1 (by norm_num)]
    unfold qC epsBar
    rw [abs_lt]
    constructor <;> norm_num
  · rw [e5, cyc2 (by norm_num)]
    unfold rC epsBar
    rw [abs_lt]
    constructor <;> norm_num
  · rw [e6, cyc0 (by norm_num)]
    unfold pC epsBar
    rw [abs_lt]
    constructor <;> norm_num
  · rw [e7, cyc1 (by norm_num)]
    unfold qC epsBar
    rw [abs_lt]
    constructor <;> norm_num
  · rw [e8, cyc2 (by norm_num)]
    unfold rC epsBar
    rw [abs_lt]
    constructor <;> norm_num
  · rw [e9, cyc0 (by norm_num)]
    unfold pC epsBar
    rw [abs_lt]
    constructor <;> norm_num
  · rw [e10, cyc1 (by norm_num)]
    unfold qC epsBar
    rw [abs_lt]
    constructor <;> norm_num
  · rw [e11, cyc2 (by norm_num)]
    unfold rC epsBar
    rw [abs_lt]
    constructor <;> norm_num
