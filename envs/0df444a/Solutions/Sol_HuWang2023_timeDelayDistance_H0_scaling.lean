-- Prove2me | solution 1 for HuWang2023.timeDelayDistance_H0_scaling
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T04:16:20.890849+00:00
-- url     : https://prove2.me/submissions/7e9b4f09-ff95-4f71-91f5-303139a65b18

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

theorem solution (c Ωm zl zs H0 H0' : ℝ)
    (hH0 : H0 ≠ 0) (hH0' : H0' ≠ 0) :
    H0 * timeDelayDistance c H0 Ωm zl zs = H0' * timeDelayDistance c H0' Ωm zl zs := by
  have hscale : ∀ h : ℝ, h ≠ 0 → ∀ a b : ℝ,
      angDistBetween c h Ωm a b = angDistBetween c 1 Ωm a b / h := by
    intro h hh a b
    unfold angDistBetween
    rw [one_mul, show c / (h * (1 + b)) = c / (1 + b) / h by rw [div_div, mul_comm]]
    ring
  have key : ∀ h : ℝ, h ≠ 0 → h * timeDelayDistance c h Ωm zl zs =
      timeDelayDistance c 1 Ωm zl zs := by
    intro h hh
    unfold timeDelayDistance angDist
    rw [hscale h hh, hscale h hh, hscale h hh]
    by_cases h0 : angDistBetween c 1 Ωm zl zs = 0
    · rw [h0]; simp
    · field_simp
  rw [key H0 hH0, key H0' hH0']
