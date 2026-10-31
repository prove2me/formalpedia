-- Prove2me | solution 1 for LogRegretOCO.ONS.ons_beta_inv_bound
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-30T19:51:34.878998+00:00
-- url     : https://prove2.me/submissions/658fb149-471c-41c8-90de-b757ed891978

import Mathlib
import Definitions.Def_LogRegretOCO_ONS_onsBeta
open LogRegretOCO.ONS

theorem solution{G D α : ℝ} (hG : 0 < G) (hD : 0 < D) (hα : 0 < α) :
    1 / onsBeta G D α ≤ 8 * (G * D + 1 / α) := by
  unfold onsBeta
  have h4 : 0 < 4 * G * D := by positivity
  rcases min_cases (1 / (4 * G * D)) α with ⟨h, _⟩ | ⟨h, hlt⟩
  · rw [h]
    rw [show 1 / (1 / 2 * (1 / (4 * G * D))) = 8 * (G * D) by field_simp; ring]
    have : 0 < 1 / α := by positivity
    linarith
  · rw [h]
    rw [show 1 / (1 / 2 * α) = 2 * (1 / α) by field_simp]
    have : 0 < G * D := by positivity
    have : 0 < 1 / α := by positivity
    nlinarith
