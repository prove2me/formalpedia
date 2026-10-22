-- Prove2me | solution 1 for MultivarScores.LevelSet.remark_2
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T09:28:07.194034+00:00
-- url     : https://prove2.me/submissions/052596c6-c3d9-4350-852c-8947eb0a7aef

import Mathlib
import Definitions.Def_MultivarScores_LevelSet_Setting

set_option autoImplicit false
open MeasureTheory

theorem solution (h : ℝ → ℝ) (hh_meas : Measurable h) (hh_nonneg : ∀ z, 0 ≤ h z)
    (hh_int : Integrable h) (α q y : ℝ) :
    (∫ z in Set.Ici q, (α - if y ≤ z then 1 else 0) * h z) + (1 - α) * ∫ z in Set.Ici y, h z =
      (α - if y < q then 1 else 0) * ∫ z in q..y, h z := by
  have hI : ∀ a b : ℝ, (∫ z in Set.Ici a, h z) - (∫ z in Set.Ici b, h z) = ∫ z in a..b, h z :=
    fun a b => intervalIntegral.integral_Ici_sub_Ici' hh_int.integrableOn hh_int.integrableOn
  have h1 : (∫ z in Set.Ici q, (α - if y ≤ z then 1 else 0) * h z) =
      α * (∫ z in Set.Ici q, h z) - ∫ z in Set.Ici (max q y), h z := by
    have e1 : ∀ z, (α - if y ≤ z then (1 : ℝ) else 0) * h z = α * h z - (Set.Ici y).indicator h z := by
      intro z
      by_cases hz : y ≤ z
      · simp [hz]; ring
      · simp [hz]
    simp_rw [e1]
    rw [integral_sub (hh_int.integrableOn.const_mul α)
      ((hh_int.indicator measurableSet_Ici).integrableOn), integral_const_mul,
      setIntegral_indicator measurableSet_Ici, Set.Ici_inter_Ici]
  rw [h1]
  rcases le_or_gt q y with hqy | hqy
  · rw [max_eq_right hqy, if_neg (not_lt.2 hqy), ← hI q y]
    ring
  · rw [max_eq_left hqy.le, if_pos hqy, ← hI q y]
    ring
