-- Prove2me | solution 1 for IQCAlg.HeavyBall.perturbation_recursion
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T07:20:48.178532+00:00
-- url     : https://prove2.me/submissions/a587b88e-2e93-4b32-afb8-767ace80843e

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

end IQHAux

open IQHAux

theorem solution (x : ℕ → ℝ) (hx : IsB1Traj x) (k : ℕ)
    (hpiece : (cyc (k + 1) < 1 → x (k + 1) < 1) ∧ (2 < cyc (k + 1) → 2 < x (k + 1))) :
    ![eps x (k + 2), eps x (k + 1)] = Pm.mulVec ![eps x (k + 1), eps x k] := by
  have h := eps_rec x hx k hpiece
  ext i
  fin_cases i
  · simp [Pm, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    linarith
  · simp [Pm, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
