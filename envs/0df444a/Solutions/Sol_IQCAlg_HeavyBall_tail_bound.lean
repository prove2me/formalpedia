-- Prove2me | solution 1 for IQCAlg.HeavyBall.tail_bound
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T07:30:26.727278+00:00
-- url     : https://prove2.me/submissions/08f39266-eddd-42eb-bf81-0b77065d8400

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

theorem solution (x : ℕ → ℝ) (hx : IsB1Traj x) (i : ℕ)
    (h8 : ∀ j : ℕ, j < 8 → eps x (i + j) ^ 2 < epsBar ^ 2) :
    ∀ k : ℕ, i ≤ k → eps x k ^ 2 < epsBar ^ 2 := by
  have hpc : ∀ j, eps x j ^ 2 < epsBar ^ 2 →
      (cyc j < 1 → x j < 1) ∧ (2 < cyc j → 2 < x j) := by
    intro j h
    have hb : |eps x j| < epsBar := abs_lt_of_sq_lt_sq h (by unfold epsBar; norm_num)
    rw [abs_lt] at hb
    unfold eps at hb
    rcases cyc_cases j with hc | hc | hc
    · rw [hc] at hb
      refine ⟨fun _ => ?_, fun h2 => ?_⟩
      · unfold pC epsBar at hb; linarith [hb.2]
      · rw [hc] at h2; linarith [p_lt]
    · rw [hc] at hb
      refine ⟨fun _ => ?_, fun h2 => ?_⟩
      · unfold qC epsBar at hb; linarith [hb.2]
      · rw [hc] at h2; linarith [q_lt]
    · rw [hc] at hb
      refine ⟨fun h2 => ?_, fun _ => ?_⟩
      · rw [hc] at h2; linarith [r_gt]
      · unfold rC epsBar at hb; linarith [hb.1]
  have hEB : 0 < epsBar ^ 2 := by unfold epsBar; norm_num
  have key : ∀ n : ℕ, ∀ j : ℕ, j < 8 → eps x (i + n + j) ^ 2 < epsBar ^ 2 := by
    intro n
    induction n with
    | zero => intro j hj; simpa using h8 j hj
    | succ n ih =>
      intro j hj
      by_cases hj7 : j < 7
      · have := ih (j + 1) (by omega)
        have e : i + n + (j + 1) = i + (n + 1) + j := by omega
        rwa [e] at this
      · have hj' : j = 7 := by omega
        subst hj'
        have hp : ∀ m : ℕ, 1 ≤ m → m ≤ 7 →
            (cyc (i + n + m) < 1 → x (i + n + m) < 1) ∧ (2 < cyc (i + n + m) → 2 < x (i + n + m)) :=
          fun m h1 h2 => hpc _ (ih m (by omega))
        have h := eps8_sq x hx (i + n) hp
        have a0 := ih 0 (by norm_num)
        have a1 := ih 1 (by norm_num)
        have e : i + (n + 1) + 7 = i + n + 8 := by omega
        rw [e]
        simp only [add_zero] at a0
        linarith
  intro k hk
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hk
  simpa using key n 0 (by norm_num)
