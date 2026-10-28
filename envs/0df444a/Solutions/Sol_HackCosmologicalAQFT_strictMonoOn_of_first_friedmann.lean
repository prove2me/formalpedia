-- Prove2me | solution 1 for HackCosmologicalAQFT.strictMonoOn_of_first_friedmann
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T12:34:17.780774+00:00
-- url     : https://prove2.me/submissions/75a8d9f4-e7b4-4756-917e-2e0361fe6496

import Mathlib
import Definitions.Def_hack_flrw_friedmann

open HackCosmologicalAQFT in
theorem solution (G : ℝ) (hG : 0 < G) (a ρ : ℝ → ℝ) (I : Set ℝ)
    (hI : IsOpen I) (hIc : IsPreconnected I)
    (ha : ContDiffOn ℝ 2 a I) (hpos : ∀ t ∈ I, 0 < a t)
    (hF1 : FirstFriedmannEq G a ρ I) (hρ : ∀ t ∈ I, 0 < ρ t)
    (t₁ : ℝ) (ht₁ : t₁ ∈ I) (hexp : 0 < deriv a t₁) :
    StrictMonoOn a I := by
  have hc : 0 < 8 * Real.pi * G / 3 := by positivity
  have hne : ∀ t ∈ I, deriv a t ≠ 0 := by
    intro t ht h
    have h1 := hF1 t ht
    rw [hubbleRate, h, zero_div, zero_pow two_ne_zero] at h1
    have h2 := mul_pos hc (hρ t ht)
    linarith
  have hcont : ContinuousOn (deriv a) I := ha.continuousOn_deriv_of_isOpen hI (by norm_num)
  have hdpos : ∀ t ∈ I, 0 < deriv a t := by
    intro t ht
    by_contra hle
    push_neg at hle
    obtain ⟨c, hcI, hc0⟩ := hIc.intermediate_value ht ht₁ hcont ⟨hle, hexp.le⟩
    exact hne c hcI hc0
  have hconv : Convex ℝ I := (isPreconnected_iff_ordConnected.mp hIc).convex
  exact strictMonoOn_of_deriv_pos hconv ha.continuousOn
    (fun x hx => hdpos x (interior_subset hx))
