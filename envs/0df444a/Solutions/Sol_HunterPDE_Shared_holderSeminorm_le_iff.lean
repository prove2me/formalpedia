-- Prove2me | solution 1 for HunterPDE.Shared.holderSeminorm_le_iff
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-10T16:29:45.651333+00:00
-- url     : https://prove2.me/submissions/3f230fde-2617-4831-af1e-2bab076e9b3f

import Definitions.Def_HunterPDE_Shared_HolderSeminorm
import Mathlib.Tactic.Positivity
open scoped ENNReal NNReal

theorem solution (n : ℕ) (α : ℝ) (Ω : Set (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (C : ℝ≥0) :
    HunterPDE.Shared.holderSeminorm α Ω f ≤ (C : ℝ≥0∞) ↔
      ∀ x ∈ Ω, ∀ y ∈ Ω, x ≠ y → |f x - f y| ≤ (C : ℝ) * ‖x - y‖ ^ α := by
  unfold HunterPDE.Shared.holderSeminorm
  rw [iSup_le_iff]
  constructor
  · intro h x hx y hy hxy
    have hp : 0 < ‖x - y‖ ^ α := Real.rpow_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hxy)) α
    have hq := (iSup_le_iff.mp (iSup_le_iff.mp (iSup_le_iff.mp (iSup_le_iff.mp (h x) hx) y) hy)) hxy
    exact (div_le_iff₀ hp).mp (ENNReal.ofReal_le_coe.mp hq)
  · intro h x
    refine iSup_le fun hx => iSup_le fun y => iSup_le fun hy => iSup_le fun hxy => ?_
    apply ENNReal.ofReal_le_coe.mpr
    exact (div_le_iff₀ (Real.rpow_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hxy)) α)).mpr (h x hx y hy hxy)
