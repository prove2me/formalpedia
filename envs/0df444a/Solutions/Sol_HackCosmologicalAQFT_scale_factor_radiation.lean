-- Prove2me | solution 1 for HackCosmologicalAQFT.scale_factor_radiation
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T12:35:04.134152+00:00
-- url     : https://prove2.me/submissions/6c2f30d3-cd16-45fa-83af-e24528d08bb8

import Mathlib
import Definitions.Def_hack_flrw_friedmann

open HackCosmologicalAQFT in
theorem solution (G : ℝ) (hG : 0 < G) (a ρ : ℝ → ℝ) (I : Set ℝ)
    (hI : IsOpen I) (hIc : IsPreconnected I)
    (ha : ContDiffOn ℝ 2 a I) (hpos : ∀ t ∈ I, 0 < a t) (hexp : ∀ t ∈ I, 0 < deriv a t)
    (hF1 : FirstFriedmannEq G a ρ I)
    (K : ℝ) (hK : 0 < K) (hρ : ∀ t ∈ I, ρ t = K / a t ^ 4) :
    ∃ C > 0, ∃ t₀ : ℝ, ∀ t ∈ I, t₀ < t ∧ a t = C * (t - t₀) ^ (1 / 2 : ℝ) := by
  have hπ := Real.pi_pos
  obtain ⟨c, hc_def⟩ : ∃ c, c = 8 * Real.pi * G / 3 := ⟨_, rfl⟩
  have hc : 0 < c := by rw [hc_def]; positivity
  obtain ⟨m, hm_def⟩ : ∃ m, m = 2 * Real.sqrt (c * K) := ⟨_, rfl⟩
  have hm : 0 < m := by rw [hm_def]; have := Real.sqrt_pos.mpr (mul_pos hc hK); positivity
  have hd : ∀ t ∈ I, HasDerivAt (fun s => a s ^ 2) m t := by
    intro t ht
    have hA := hpos t ht
    have hda : HasDerivAt a (deriv a t) t :=
      ((ha.differentiableOn (by norm_num)).differentiableAt (hI.mem_nhds ht)).hasDerivAt
    have h := hda.pow 2
    refine h.congr_deriv ?_
    have hF := hF1 t ht
    rw [hubbleRate, hρ t ht, ← hc_def] at hF
    have hkey : (a t * deriv a t) ^ 2 = c * K := by
      have : (a t * deriv a t) ^ 2 = (deriv a t / a t) ^ 2 * a t ^ 4 := by
        field_simp
      rw [this, hF]; field_simp
    rw [hm_def, ← hkey, Real.sqrt_sq (mul_nonneg hA.le (hexp t ht).le)]
    simp; ring
  have hlin : ∀ t ∈ I, HasDerivAt (fun s => a s ^ 2 - m * s) 0 t := fun t ht => by
    have := (hd t ht).sub ((hasDerivAt_id t).const_mul m)
    simp only [mul_one, sub_self] at this
    exact this
  obtain ⟨c0, hc0⟩ := hI.exists_is_const_of_deriv_eq_zero hIc
    (f := fun s => a s ^ 2 - m * s)
    (fun t ht => (hlin t ht).differentiableAt.differentiableWithinAt)
    (fun t ht => by simp only [Pi.zero_apply]; exact (hlin t ht).deriv)
  have hg : ∀ t ∈ I, a t ^ 2 = m * (t - (-c0 / m)) := by
    intro t ht
    have := hc0 t ht
    try simp only at this
    rw [show m * (t - (-c0 / m)) = m * t + c0 by field_simp; ring]
    linarith
  refine ⟨m ^ (1 / 2 : ℝ), Real.rpow_pos_of_pos hm _, -c0 / m, fun t ht => ?_⟩
  have hgt := hg t ht
  have hpos' : 0 < a t ^ 2 := pow_pos (hpos t ht) _
  have htt : 0 < t - -c0 / m := by
    rw [hgt] at hpos'; exact pos_of_mul_pos_right hpos' hm.le
  refine ⟨by linarith, ?_⟩
  rw [← Real.mul_rpow hm.le htt.le, ← hgt, ← Real.sqrt_eq_rpow, Real.sqrt_sq (hpos t ht).le]
