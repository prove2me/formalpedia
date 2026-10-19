-- Prove2me | solution 1 for HuWang2023.timeDelayDistance_determines_H0
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T04:18:04.760294+00:00
-- url     : https://prove2.me/submissions/e1506c63-d4ae-44ae-bf7e-8f386b62385c

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
theorem solution (c Ωm zl zs : ℝ) (hc : 0 < c)
    (hΩm0 : 0 ≤ Ωm) (hzl : 0 < zl) (hzls : zl < zs) :
    ∃ K : ℝ, 0 < K ∧ ∀ H0 : ℝ, 0 < H0 → timeDelayDistance c H0 Ωm zl zs = K / H0 := by
  have hscale : ∀ h : ℝ, h ≠ 0 → ∀ a b : ℝ,
      angDistBetween c h Ωm a b = angDistBetween c 1 Ωm a b / h := by
    intro h hh a b
    unfold angDistBetween
    rw [one_mul, show c / (h * (1 + b)) = c / (1 + b) / h by rw [div_div, mul_comm]]
    ring
  have hpos : ∀ a b : ℝ, 0 ≤ a → a < b → 0 < angDistBetween c 1 Ωm a b := by
    intro a b ha hab
    unfold angDistBetween
    apply mul_pos (div_pos hc (mul_pos one_pos (by linarith)))
    apply intervalIntegral.intervalIntegral_pos_of_pos_on
      (intervalIntegrable_inv_flatE Ωm a b hΩm0 ha (by linarith)) _ hab
    intro z hz
    exact inv_pos.mpr (flatE_pos Ωm z hΩm0 (by linarith [hz.1]))
  refine ⟨timeDelayDistance c 1 Ωm zl zs, ?_, fun H0 hH0 => ?_⟩
  · unfold timeDelayDistance angDist
    have h1 := hpos 0 zl le_rfl hzl
    have h2 := hpos 0 zs le_rfl (by linarith)
    have h3 := hpos zl zs hzl.le hzls
    have : 0 < 1 + zl := by linarith
    positivity
  · unfold timeDelayDistance angDist
    rw [hscale H0 hH0.ne', hscale H0 hH0.ne', hscale H0 hH0.ne']
    have h3 := (hpos zl zs hzl.le hzls).ne'
    field_simp
