-- Prove2me | solution 1 for HuWang2023.angDistBetween_eq_flat
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T04:16:13.085897+00:00
-- url     : https://prove2.me/submissions/360bdda9-8acf-4c14-92ff-f97bc0f0a402

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

open HuWangAux in
theorem solution (c H0 Ωm zl zs : ℝ)
    (hΩm0 : 0 ≤ Ωm) (hzl : 0 ≤ zl) (hzls : zl ≤ zs) :
    angDistBetween c H0 Ωm zl zs =
      angDist c H0 Ωm zs - (1 + zl) / (1 + zs) * angDist c H0 Ωm zl := by
  unfold angDist angDistBetween
  have hzs : 0 ≤ zs := le_trans hzl hzls
  have hsplit := intervalIntegral.integral_interval_sub_left
    (intervalIntegrable_inv_flatE Ωm 0 zs hΩm0 le_rfl hzs)
    (intervalIntegrable_inv_flatE Ωm 0 zl hΩm0 le_rfl hzl)
  rw [← hsplit]
  have h1 : (1 + zl) ≠ 0 := by linarith
  have h2 : (1 + zs) ≠ 0 := by linarith
  rw [show c / (H0 * (1 + zl)) = c / H0 / (1 + zl) by rw [div_div],
    show c / (H0 * (1 + zs)) = c / H0 / (1 + zs) by rw [div_div]]
  field_simp
