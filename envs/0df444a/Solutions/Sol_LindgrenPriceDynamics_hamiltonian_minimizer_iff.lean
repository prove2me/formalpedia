-- Prove2me | solution 1 for LindgrenPriceDynamics.hamiltonian_minimizer_iff
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T05:34:19.804806+00:00
-- url     : https://prove2.me/submissions/3103a0de-fdb5-462d-b22c-30122a136418

import Mathlib
import Definitions.Def_LindgrenPriceDynamics

open LindgrenPriceDynamics in
theorem c4084ad6_diff {l : ℕ} (m E : ℝ) (g v w : Fin l → ℝ) :
    hamiltonian m E g w - hamiltonian m E g v =
      ∑ i, ((m / 2) * (w i - v i) ^ 2 + (m * v i + g i) * (w i - v i)) := by
  unfold hamiltonian dot
  have h1 : (1 / 2) * m * ∑ i, w i * w i + E + ∑ i, g i * w i
      - ((1 / 2) * m * ∑ i, v i * v i + E + ∑ i, g i * v i)
      = ∑ i, ((1 / 2) * m * (w i * w i) + g i * w i
          - ((1 / 2) * m * (v i * v i) + g i * v i)) := by
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum]
    ring
  rw [h1]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  ring

open LindgrenPriceDynamics in
theorem solution {l : ℕ} (m : ℝ) (hm : 0 < m) (E : ℝ) (g v : Fin l → ℝ) :
    IsMinOn (hamiltonian m E g) Set.univ v ↔ ∀ i, m * v i = -g i := by
  constructor
  · intro hmin i
    set a := m * v i + g i with ha
    let w : Fin l → ℝ := Function.update v i (v i - a / m)
    have hle : hamiltonian m E g v ≤ hamiltonian m E g w :=
      (isMinOn_iff.mp hmin) w (Set.mem_univ _)
    have hd := c4084ad6_diff m E g v w
    have hs : ∑ j, ((m / 2) * (w j - v j) ^ 2 + (m * v j + g j) * (w j - v j))
        = (m / 2) * (w i - v i) ^ 2 + (m * v i + g i) * (w i - v i) := by
      refine Finset.sum_eq_single i (fun j _ hj => ?_) (fun h => absurd (Finset.mem_univ i) h)
      have : w j = v j := by simp [w, Function.update_of_ne hj]
      rw [this]; ring
    have hwi : w i - v i = -(a / m) := by simp [w]
    rw [hs, hwi, ← ha] at hd
    have hm0 : m ≠ 0 := ne_of_gt hm
    have key : (m / 2) * (-(a / m)) ^ 2 + a * (-(a / m)) = -(a ^ 2 / (2 * m)) := by
      field_simp; ring
    rw [key] at hd
    have hq : a ^ 2 / (2 * m) ≤ 0 := by linarith
    have hq2 : 0 ≤ a ^ 2 / (2 * m) := by positivity
    have h0 : a ^ 2 / (2 * m) = 0 := le_antisymm hq hq2
    have : a ^ 2 = 0 := by
      rcases div_eq_zero_iff.mp h0 with h | h
      · exact h
      · exfalso; linarith
    have : a = 0 := pow_eq_zero_iff (two_ne_zero) |>.mp this
    linarith
  · intro h
    refine isMinOn_iff.mpr (fun w _ => ?_)
    have hd := c4084ad6_diff m E g v w
    have hnn : 0 ≤ ∑ j, ((m / 2) * (w j - v j) ^ 2 + (m * v j + g j) * (w j - v j)) := by
      refine Finset.sum_nonneg (fun j _ => ?_)
      have : m * v j + g j = 0 := by linarith [h j]
      rw [this]
      have : 0 ≤ (m / 2) * (w j - v j) ^ 2 := by positivity
      linarith
    linarith
