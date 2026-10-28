-- Prove2me | solution 1 for HackCosmologicalAQFT.continuity_eq_of_friedmann
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T12:34:36.165503+00:00
-- url     : https://prove2.me/submissions/0e9c920c-ba54-49ee-9c1a-d84f5e6785f6

import Mathlib
import Definitions.Def_hack_flrw_friedmann

open HackCosmologicalAQFT in
theorem solution (G : ℝ) (hG : 0 < G) (a ρ p : ℝ → ℝ) (I : Set ℝ)
    (hI : IsOpen I) (ha : ContDiffOn ℝ 2 a I) (hpos : ∀ t ∈ I, 0 < a t)
    (hF1 : FirstFriedmannEq G a ρ I) (hF2 : SecondFriedmannEq G a ρ p I) :
    ∀ t ∈ I, deriv ρ t + 3 * hubbleRate a t * (ρ t + p t) = 0 := by
  intro t ht
  have hπ := Real.pi_pos
  have hc : (8 * Real.pi * G / 3) ≠ 0 := by positivity
  have heq : ρ =ᶠ[nhds t] fun s => 3 / (8 * Real.pi * G) * (deriv a s / a s) ^ 2 := by
    filter_upwards [hI.mem_nhds ht] with s hs
    have h1 := hF1 s hs
    rw [hubbleRate] at h1
    rw [h1]; field_simp
  have hda : HasDerivAt a (deriv a t) t :=
    ((ha.differentiableOn (by norm_num)).differentiableAt (hI.mem_nhds ht)).hasDerivAt
  have hdda : HasDerivAt (deriv a) (deriv (deriv a) t) t :=
    (((ha.deriv_of_isOpen hI (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).differentiableOn
      (by norm_num)).differentiableAt (hI.mem_nhds ht)).hasDerivAt
  have hat := (hpos t ht).ne'
  have hD := (((hdda.div hda hat).pow 2).const_mul (3 / (8 * Real.pi * G)))
  have hD' := hD.deriv
  simp only [Pi.div_apply, Pi.pow_apply, show (2:ℕ) - 1 = 1 from rfl, pow_one, Nat.cast_ofNat] at hD'
  rw [heq.deriv_eq, hD']
  have h2 := hF2 t ht
  have h1 := hF1 t ht
  rw [hubbleRate] at h1 ⊢
  have hE : deriv (deriv a) t = -(4 * Real.pi * G / 3) * (ρ t + 3 * p t) * a t := by
    rw [← h2]; field_simp
  have hρt : ρ t = 3 * deriv a t ^ 2 / (8 * Real.pi * G * a t ^ 2) := by
    rw [div_pow] at h1
    field_simp at h1 ⊢
    linarith
  rw [hE, hρt]
  field_simp
  ring
