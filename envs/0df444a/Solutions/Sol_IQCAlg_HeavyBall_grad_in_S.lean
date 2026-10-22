-- Prove2me | solution 1 for IQCAlg.HeavyBall.grad_in_S
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T07:35:38.924537+00:00
-- url     : https://prove2.me/submissions/90ebede8-ad67-435c-93bc-aa88f00f815e

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

lemma gradF_eq (x : ℝ) : gradF x = x + 24 + 24 * min (x - 1) 0 + 24 * max (x - 2) 0 := by
  unfold gradF
  split_ifs with h1 h2
  · rw [min_eq_left (by linarith), max_eq_right (by linarith)]; ring
  · rw [min_eq_right (by linarith), max_eq_right (by linarith)]; ring
  · rw [min_eq_right (by linarith), max_eq_left (by linarith)]; ring

lemma gradF_cont : Continuous gradF := by
  have : gradF = fun x => x + 24 + 24 * min (x - 1) 0 + 24 * max (x - 2) 0 := funext gradF_eq
  rw [this]; fun_prop

lemma gradF_lip (x y : ℝ) : |gradF x - gradF y| ≤ 25 * |x - y| := by
  unfold gradF
  rcases abs_cases (x - y) with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;>
  split_ifs <;> rw [abs_le] <;> constructor <;> linarith

lemma gradF_sub_mono : Monotone (fun x => gradF x - x) := by
  intro a b hab
  simp only [gradF_eq]
  have h1 : min (a - 1) 0 ≤ min (b - 1) 0 := min_le_min (by linarith) le_rfl
  have h2 : max (a - 2) 0 ≤ max (b - 2) 0 := max_le_max (by linarith) le_rfl
  linarith

theorem solution (f : ℝ → ℝ) (hf : ∀ x : ℝ, HasDerivAt f (gradF x) x) :
    InSmL1 f 1 25 := by
  have hd : ∀ x, deriv f x = gradF x := fun x => (hf x).deriv
  have hdiff : Differentiable ℝ f := fun x => (hf x).differentiableAt
  have hderiv : deriv f = gradF := funext hd
  refine ⟨by norm_num, by norm_num, ?_, ?_, ?_⟩
  · rw [contDiff_one_iff_deriv]
    exact ⟨hdiff, by rw [hderiv]; exact gradF_cont⟩
  · rw [strongConvexOn_iff_convex]
    have hg : ∀ x, HasDerivAt (fun x : ℝ => f x - 1 / 2 * ‖x‖ ^ 2) (gradF x - x) x := by
      intro x
      have h2 : HasDerivAt (fun x : ℝ => 1 / 2 * ‖x‖ ^ 2) x x := by
        have h3 := ((hasDerivAt_pow 2 x).const_mul (1 / 2 : ℝ))
        have e : (fun x : ℝ => 1 / 2 * ‖x‖ ^ 2) = fun x : ℝ => 1 / 2 * x ^ 2 := by
          funext y; simp [Real.norm_eq_abs, sq_abs]
        rw [e]
        refine h3.congr_deriv ?_
        norm_num; ring
      exact (hf x).sub h2
    apply MonotoneOn.convexOn_of_deriv convex_univ
    · exact (fun x _ => (hg x).continuousAt.continuousWithinAt)
    · exact (fun x _ => (hg x).differentiableAt.differentiableWithinAt)
    · intro a _ b _ hab
      rw [(hg a).deriv, (hg b).deriv]
      exact gradF_sub_mono hab
  · intro x y
    rw [hd, hd]
    exact gradF_lip x y
