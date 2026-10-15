-- Prove2me | solution 1 for Multihoming.Thresholds.eLow_lt_eP
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-14T12:39:12.745115+00:00
-- url     : https://prove2.me/submissions/10aa0248-e388-44bb-b973-fa3de6b90e00

import Mathlib
import Definitions.Def_Multihoming_Thresholds_Model
open Multihoming.Thresholds

theorem solution(t μ : ℝ) (ht : 0 < t) (hμ : 0 ≤ μ) (hμt : μ < t) :
    eP t μ - eLow t μ = (t - μ) * (2 * t - μ) / (2 * t) ∧ eLow t μ < eP t μ := by
  have key : eP t μ - eLow t μ = (t - μ) * (2 * t - μ) / (2 * t) := by
    unfold eP eLow
    field_simp
    ring
  refine ⟨key, ?_⟩
  have hp : 0 < (t - μ) * (2 * t - μ) / (2 * t) := div_pos (mul_pos (by linarith) (by linarith)) (by linarith)
  linarith
