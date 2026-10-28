-- Prove2me | solution 1 for HackCosmologicalAQFT.scale_factor_cosmological_constant
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T12:34:27.149162+00:00
-- url     : https://prove2.me/submissions/07212ad7-eb24-40a5-95ae-e606f1b1a3d2

import Mathlib
import Definitions.Def_hack_flrw_friedmann

open HackCosmologicalAQFT in
theorem solution (G : ℝ) (hG : 0 < G) (a ρ : ℝ → ℝ) (I : Set ℝ)
    (hI : IsOpen I) (hIc : IsPreconnected I)
    (ha : ContDiffOn ℝ 2 a I) (hpos : ∀ t ∈ I, 0 < a t) (hexp : ∀ t ∈ I, 0 < deriv a t)
    (hF1 : FirstFriedmannEq G a ρ I)
    (Λ : ℝ) (hΛ : 0 < Λ) (hρ : ∀ t ∈ I, ρ t = Λ / (8 * Real.pi * G)) :
    ∃ C > 0, ∀ t ∈ I, a t = C * Real.exp (Real.sqrt (Λ / 3) * t) := by
  have hπ := Real.pi_pos
  have hH : ∀ t ∈ I, deriv a t / a t = Real.sqrt (Λ / 3) := by
    intro t ht
    have h1 := hF1 t ht
    rw [hubbleRate, hρ t ht] at h1
    have h2 : (deriv a t / a t) ^ 2 = Λ / 3 := by
      rw [h1]; field_simp
    have h3 : 0 < deriv a t / a t := div_pos (hexp t ht) (hpos t ht)
    rw [← h2, Real.sqrt_sq h3.le]
  have hd : ∀ t ∈ I, HasDerivAt (fun s => Real.log (a s) - Real.sqrt (Λ / 3) * s) 0 t := by
    intro t ht
    have hda : HasDerivAt a (deriv a t) t :=
      ((ha.differentiableOn (by norm_num)).differentiableAt (hI.mem_nhds ht)).hasDerivAt
    have := (hda.log (hpos t ht).ne').sub ((hasDerivAt_id t).const_mul (Real.sqrt (Λ / 3)))
    refine this.congr_deriv ?_
    rw [hH t ht]; simp
  obtain ⟨c, hc⟩ := hI.exists_is_const_of_deriv_eq_zero hIc
    (fun t ht => (hd t ht).differentiableAt.differentiableWithinAt)
    (fun t ht => by simp only [Pi.zero_apply]; exact (hd t ht).deriv)
  refine ⟨Real.exp c, Real.exp_pos c, fun t ht => ?_⟩
  have h := hc t ht
  try simp only at h
  rw [← Real.exp_add, ← h, sub_add_cancel, Real.exp_log (hpos t ht)]
