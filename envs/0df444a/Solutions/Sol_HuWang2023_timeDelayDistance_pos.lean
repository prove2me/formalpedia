-- Prove2me | solution 1 for HuWang2023.timeDelayDistance_pos
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T04:16:28.454298+00:00
-- url     : https://prove2.me/submissions/03438a59-a60a-44bc-97a6-1b772e8df0c6

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
theorem solution (c H0 Ωm zl zs : ℝ) (hc : 0 < c) (hH0 : 0 < H0)
    (hΩm0 : 0 ≤ Ωm) (hzl : 0 < zl) (hzls : zl < zs) :
    0 < timeDelayDistance c H0 Ωm zl zs := by
  have hpos : ∀ a b : ℝ, 0 ≤ a → a < b → 0 < angDistBetween c H0 Ωm a b := by
    intro a b ha hab
    unfold angDistBetween
    apply mul_pos (div_pos hc (mul_pos hH0 (by linarith)))
    apply intervalIntegral.intervalIntegral_pos_of_pos_on
      (intervalIntegrable_inv_flatE Ωm a b hΩm0 ha (by linarith)) _ hab
    intro z hz
    exact inv_pos.mpr (flatE_pos Ωm z hΩm0 (by linarith [hz.1]))
  unfold timeDelayDistance angDist
  have h1 := hpos 0 zl le_rfl hzl
  have h2 := hpos 0 zs le_rfl (by linarith)
  have h3 := hpos zl zs hzl.le hzls
  have : 0 < 1 + zl := by linarith
  positivity
