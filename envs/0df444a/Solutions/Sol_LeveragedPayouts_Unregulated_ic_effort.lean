-- Prove2me | solution 1 for LeveragedPayouts.Unregulated.ic_effort
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-14T13:46:44.609985+00:00
-- url     : https://prove2.me/submissions/dfe3520f-b47d-4ee4-9c69-ec05b760ba2c

import Mathlib
import Definitions.Def_LeveragedPayouts_Unregulated_Firm
open LeveragedPayouts.Unregulated

theorem solution(π : ℝ) (hπ : 0 < π) (x e : ℝ) : IsIC π x e ↔ e = π * x := by
  unfold IsIC
  have h2 : (0:ℝ) < 2 * π := by positivity
  constructor
  · intro h
    have h' := h (π * x)
    have eq : x * (π * x) - (π * x) ^ 2 / (2 * π) - (x * e - e ^ 2 / (2 * π)) = (e - π * x) ^ 2 / (2 * π) := by
      field_simp; ring
    have key : (e - π * x) ^ 2 / (2 * π) ≤ 0 := by linarith
    have hsq : (e - π * x) ^ 2 ≤ 0 := by
      have := (div_le_iff₀ h2).mp key; linarith
    nlinarith [sq_nonneg (e - π * x)]
  · rintro rfl y
    have eq : x * (π * x) - (π * x) ^ 2 / (2 * π) - (x * y - y ^ 2 / (2 * π)) = (y - π * x) ^ 2 / (2 * π) := by
      field_simp; ring
    have : 0 ≤ (y - π * x) ^ 2 / (2 * π) := by positivity
    linarith
