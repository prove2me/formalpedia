-- Prove2me | solution 1 for GlobalTheory.schur_scalar_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:32:46.588894+00:00
-- url     : https://prove2.me/submissions/acaa87f0-8bfa-48d5-b1b5-b587aa728dab

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_SchurComplementBlockQuadraticLowerBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ComplexOrder
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (u w C₀ c₀ : ℝ) (hC : 0 ≤ C₀) (hc : 0 < c₀) :
    u ^ 2 + w ^ 2 ≤ (1 + C₀ / c₀) ^ 2 * max 1 (1 / c₀) *
      ((1 + C₀ ^ 2 / c₀) * u ^ 2 - 2 * C₀ * u * w + c₀ * w ^ 2) := by
  set α := C₀ / c₀ with hα
  have hα0 : 0 ≤ α := div_nonneg hC hc.le
  set p := w - α * u with hp
  have e : (1 + C₀ ^ 2 / c₀) * u ^ 2 - 2 * C₀ * u * w + c₀ * w ^ 2 = u ^ 2 + c₀ * p ^ 2 := by
    rw [hp, hα]; field_simp; ring
  have hw : w = p + α * u := by rw [hp]; ring
  have h1 : u ^ 2 + w ^ 2 ≤ (1 + α) ^ 2 * (u ^ 2 + p ^ 2) := by
    rw [hw]
    nlinarith [mul_nonneg hα0 (sq_nonneg (p - u)), mul_nonneg hα0 (sq_nonneg u),
      mul_nonneg (mul_nonneg hα0 hα0) (sq_nonneg u), mul_nonneg hα0 (sq_nonneg p),
      mul_nonneg (mul_nonneg hα0 hα0) (sq_nonneg p)]
  set M := max 1 (1 / c₀) with hM
  have hM1 : 1 ≤ M := le_max_left _ _
  have hMc : 1 ≤ M * c₀ := by
    have : 1 / c₀ ≤ M := le_max_right _ _
    rw [div_le_iff₀ hc] at this; linarith
  have h2 : u ^ 2 + p ^ 2 ≤ M * (u ^ 2 + c₀ * p ^ 2) := by
    nlinarith [mul_le_mul_of_nonneg_right hM1 (sq_nonneg u),
      mul_le_mul_of_nonneg_right hMc (sq_nonneg p)]
  rw [e]
  calc u ^ 2 + w ^ 2 ≤ (1 + α) ^ 2 * (u ^ 2 + p ^ 2) := h1
    _ ≤ (1 + α) ^ 2 * (M * (u ^ 2 + c₀ * p ^ 2)) :=
        mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
    _ = _ := by ring
end GlobalTheory
