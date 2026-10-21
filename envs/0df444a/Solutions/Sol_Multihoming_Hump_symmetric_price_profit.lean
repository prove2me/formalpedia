-- Prove2me | solution 1 for Multihoming.Hump.symmetric_price_profit
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T04:35:18.214519+00:00
-- url     : https://prove2.me/submissions/5dda253e-e6a5-431e-88af-01cbe56be147

import Mathlib
import Definitions.Def_Multihoming_Hump_Model
set_option autoImplicit false


theorem solution (t μ e : ℝ) (ht : 0 < t) (hμ0 : 0 ≤ μ) (hμt : μ < t) :
    Multihoming.Thresholds.reactM t μ e (Multihoming.Thresholds.pM t μ e) = Multihoming.Thresholds.pM t μ e ∧
    Multihoming.Thresholds.demandM t μ e (Multihoming.Thresholds.pM t μ e) (Multihoming.Thresholds.pM t μ e) = t * (μ + e) / ((2 * t - μ) * (t + μ)) ∧
    Multihoming.Hump.piM t μ e = Multihoming.Thresholds.pM t μ e * Multihoming.Thresholds.demandM t μ e (Multihoming.Thresholds.pM t μ e) (Multihoming.Thresholds.pM t μ e) := by
  open Multihoming.Thresholds in
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
  refine ⟨hR, hD, ?_⟩
  rw [hD]
  unfold Multihoming.Hump.piM pM
  field_simp
  ring
