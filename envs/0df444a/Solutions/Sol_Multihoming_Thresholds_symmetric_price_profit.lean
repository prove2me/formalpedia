-- Prove2me | solution 1 for Multihoming.Thresholds.symmetric_price_profit
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T04:05:52.26687+00:00
-- url     : https://prove2.me/submissions/7bb9017e-b384-456f-ac12-5d960e9d45eb

import Mathlib
import Definitions.Def_Multihoming_Thresholds_Model
set_option autoImplicit false
open Multihoming.Thresholds

theorem solution (t μ e : ℝ) (ht : 0 < t) (hμ : 0 ≤ μ) (hμt : μ < t) :
    reactM t μ e (pM t μ e) = pM t μ e ∧
    (∀ p : ℝ, p * demandM t μ e p (pM t μ e) ≤
      pM t μ e * demandM t μ e (pM t μ e) (pM t μ e)) ∧
    demandM t μ e (pM t μ e) (pM t μ e) = t * (μ + e) / ((2 * t - μ) * (t + μ)) ∧
    piM t μ e = t * (t - μ) * (e + μ) ^ 2 / ((t + μ) * (2 * t - μ) ^ 2) := by
  have a1 : t + μ ≠ 0 := by linarith
  have a2 : t - μ ≠ 0 := by linarith
  have a3 : 2 * t - μ ≠ 0 := by linarith
  have a5 : t ≠ 0 := ht.ne'
  have e1 : t * 2 - μ ≠ 0 := by linarith
  have h5 : t ^ 2 - μ ^ 2 = (t - μ) * (t + μ) := by ring
  have hR : reactM t μ e (pM t μ e) = pM t μ e := by
    unfold reactM pM
    field_simp
    ring
  have hD : demandM t μ e (pM t μ e) (pM t μ e) = t * (μ + e) / ((2 * t - μ) * (t + μ)) := by
    unfold demandM pM
    rw [h5]
    field_simp
    ring
  refine ⟨hR, ?_, hD, ?_⟩
  · intro p
    have hg : 0 < t / (t ^ 2 - μ ^ 2) := by
      apply div_pos ht; nlinarith
    obtain ⟨γ, hγ⟩ : ∃ γ : ℝ, γ = t / (t ^ 2 - μ ^ 2) := ⟨_, rfl⟩
    obtain ⟨κ, hκ⟩ : ∃ κ : ℝ, κ = μ / (t + μ) + t * e / (t ^ 2 - μ ^ 2) -
        μ * (e - pM t μ e) / (t ^ 2 - μ ^ 2) := ⟨_, rfl⟩
    have hD' : ∀ x, demandM t μ e x (pM t μ e) = κ - γ * x := by
      intro x; unfold demandM; rw [hκ, hγ]; ring
    have hR' : reactM t μ e (pM t μ e) * (2 * γ) = κ := by
      unfold reactM
      rw [hκ, hγ, h5]
      field_simp
      ring
    rw [hD', hD']
    rw [← hR]
    set R := reactM t μ e (pM t μ e)
    have : R * (κ - γ * R) - p * (κ - γ * p) = γ * (p - R) ^ 2 := by
      rw [← hR']; ring
    have h3 : 0 ≤ γ * (p - R) ^ 2 := mul_nonneg (by rw [hγ]; exact hg.le) (sq_nonneg _)
    linarith
  · unfold piM
    rw [hD]
    unfold pM
    field_simp
    ring
