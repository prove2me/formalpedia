-- Prove2me | solution 1 for HackCosmologicalAQFT.energy_density_scaling
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T12:34:52.955103+00:00
-- url     : https://prove2.me/submissions/ddc236a8-5ed0-4c01-b60f-c56f7bc7be07

import Mathlib
import Definitions.Def_hack_flrw_friedmann

open HackCosmologicalAQFT in
theorem solution (a ρ p : ℝ → ℝ) (w : ℝ) (hw : w = 1 / 3 ∨ w = 0 ∨ w = -1)
    (I : Set ℝ) (hI : IsOpen I) (hIc : IsPreconnected I)
    (ha : ContDiffOn ℝ 2 a I) (hpos : ∀ t ∈ I, 0 < a t)
    (hρ : DifferentiableOn ℝ ρ I) (hp : ∀ t ∈ I, p t = w * ρ t)
    (hcons : ∀ t ∈ I, deriv ρ t + 3 * hubbleRate a t * (ρ t + p t) = 0) :
    ∃ C : ℝ, ∀ t ∈ I, ρ t = C * a t ^ (-(3 * (1 + w))) := by
  have hd : ∀ t ∈ I, HasDerivAt (fun s => ρ s * a s ^ (3 * (1 + w))) 0 t := by
    intro t ht
    have hA := (hpos t ht).ne'
    have hda : HasDerivAt a (deriv a t) t :=
      ((ha.differentiableOn (by norm_num)).differentiableAt (hI.mem_nhds ht)).hasDerivAt
    have hdρ : HasDerivAt ρ (deriv ρ t) t := (hρ.differentiableAt (hI.mem_nhds ht)).hasDerivAt
    have h := hdρ.mul (hda.rpow_const (p := 3 * (1 + w)) (Or.inl hA))
    refine h.congr_deriv ?_
    have hc := hcons t ht
    rw [hubbleRate, hp t ht] at hc
    have hρ' : deriv ρ t = -(3 * (deriv a t / a t) * (ρ t + w * ρ t)) := by linarith
    rw [Real.rpow_sub_one hA, hρ']
    field_simp
    ring
  obtain ⟨C, hC⟩ := hI.exists_is_const_of_deriv_eq_zero hIc
    (fun t ht => (hd t ht).differentiableAt.differentiableWithinAt)
    (fun t ht => by simp only [Pi.zero_apply]; exact (hd t ht).deriv)
  refine ⟨C, fun t ht => ?_⟩
  have h := hC t ht
  try simp only at h
  have hApos := Real.rpow_pos_of_pos (hpos t ht) (3 * (1 + w))
  rw [Real.rpow_neg (hpos t ht).le, ← h]
  field_simp
