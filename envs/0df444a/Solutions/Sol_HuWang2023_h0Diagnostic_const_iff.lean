-- Prove2me | solution 1 for HuWang2023.h0Diagnostic_const_iff
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T04:17:07.22588+00:00
-- url     : https://prove2.me/submissions/8778e04d-9e52-46e4-91cf-f1db59cb8b2d

import Mathlib
import Definitions.Def_HuWang2023_HubbleTension_Defs
open HuWang2023

namespace HuWangAux

lemma inner_ge_one (Ωm z : ℝ) (hΩ : 0 ≤ Ωm) (hz : 0 ≤ z) : 1 ≤ Ωm * (1 + z) ^ 3 + (1 - Ωm) := by
  have : 1 ≤ (1 + z) ^ 3 := one_le_pow₀ (by linarith)
  nlinarith

lemma flatE_pos (Ωm z : ℝ) (hΩ : 0 ≤ Ωm) (hz : 0 ≤ z) : 0 < flatE Ωm z := by
  unfold flatE
  exact Real.sqrt_pos.mpr (by linarith [inner_ge_one Ωm z hΩ hz])

lemma continuousOn_inv_flatE (Ωm : ℝ) (hΩ : 0 ≤ Ωm) :
    ContinuousOn (fun z => (flatE Ωm z)⁻¹) (Set.Ici 0) := by
  apply ContinuousOn.inv₀
  · unfold flatE; fun_prop
  · intro z hz; exact (flatE_pos Ωm z hΩ hz).ne'

lemma intervalIntegrable_inv_flatE (Ωm a b : ℝ) (hΩ : 0 ≤ Ωm) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    IntervalIntegrable (fun z => (flatE Ωm z)⁻¹) MeasureTheory.volume a b := by
  apply ContinuousOn.intervalIntegrable
  apply (continuousOn_inv_flatE Ωm hΩ).mono
  intro z hz
  rw [Set.mem_uIcc] at hz
  simp only [Set.mem_Ici]
  rcases hz with ⟨h1, _⟩ | ⟨h1, _⟩ <;> linarith

end HuWangAux

theorem solution (Ωm0 H0 : ℝ) (H : ℝ → ℝ)
    (hΩm0 : 0 ≤ Ωm0) :
    (∀ z, 0 ≤ z → h0Diagnostic Ωm0 H z = H0) ↔ (∀ z, 0 ≤ z → H z = flatHubble H0 Ωm0 z) := by
  have hs : ∀ z : ℝ, 0 ≤ z →
      Real.sqrt (1 - Ωm0 + Ωm0 * (1 + z) ^ 3) = flatE Ωm0 z := by
    intro z _; unfold flatE; congr 1; ring
  have hpos : ∀ z : ℝ, 0 ≤ z → 0 < flatE Ωm0 z := fun z hz => HuWangAux.flatE_pos Ωm0 z hΩm0 hz
  constructor
  · intro h z hz
    have := h z hz
    unfold h0Diagnostic at this
    rw [hs z hz, div_eq_iff (hpos z hz).ne'] at this
    unfold flatHubble; exact this
  · intro h z hz
    unfold h0Diagnostic
    rw [hs z hz, h z hz]
    unfold flatHubble
    field_simp [(hpos z hz).ne']
