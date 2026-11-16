-- Prove2me | solution 1 for Kyprianou.Ch01.queueLaplaceExponent_rootUnique
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T21:00:02.513695+00:00
-- url     : https://prove2.me/submissions/cc04c4e3-3aab-4dc9-aef8-b1c5e020cf50

import Mathlib
import Definitions.Def_Kyprianou_Ch01_RiskQueueCore
import Theorems.Thm_Kyprianou_Ch01_queueLaplaceExponent_strictConvex
import Theorems.Thm_Kyprianou_Ch01_queueLaplaceExponent_zero

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

private theorem queueRootUniqueAux
    (f : ℝ → ℝ)
    (hsc : StrictConvexOn ℝ (Set.Ici (0 : ℝ)) f)
    (hzero : f 0 = 0) :
    ∀ x y : ℝ, 0 < x → 0 < y → f x = 0 → f y = 0 → x = y := by
  have hforbid : ∀ x y : ℝ, 0 < x → x < y →
      f x = 0 → f y = 0 → False := by
    intro x y hx hxy hfx hfy
    have hy : 0 < y := lt_trans hx hxy
    have hweightA : 0 < (y - x) / y :=
      div_pos (sub_pos.mpr hxy) hy
    have hweightB : 0 < x / y := div_pos hx hy
    have hsum : (y - x) / y + x / y = (1 : ℝ) := by
      field_simp [ne_of_gt hy] <;> ring
    have hcombo :
        ((y - x) / y) • (0 : ℝ) + (x / y) • y = x := by
      simp only [smul_eq_mul, mul_zero, zero_add]
      field_simp [ne_of_gt hy] <;> ring
    have hlt := hsc.lt_on_open_segment'
      (x := (0 : ℝ)) (y := y)
      (by simp) (by simpa using hy.le)
      (ne_of_lt hy) hweightA hweightB hsum
    rw [hcombo, hzero, hfy] at hlt
    norm_num [hfx] at hlt
  intro x y hx hy hfx hfy
  rcases lt_trichotomy x y with hlt | heq | hgt
  · exact False.elim (hforbid x y hx hlt hfx hfy)
  · exact heq
  · exact False.elim (hforbid y x hy hgt hfy hfx)

theorem solution
    (rate : ℝ≥0) (hrate : 0 < rate)
    (F : Measure ℝ) [IsProbabilityMeasure F]
    (hpositive : F (Set.Iic (0 : ℝ)) = 0)
    (hfiniteMean : Integrable (fun x : ℝ => x) F)
    (mu : ℝ) (hmu : 0 < mu)
    (hmean : (∫ x, x ∂F) = mu) :
    ∀ theta theta' : ℝ,
      0 < theta → 0 < theta' →
      queueLaplaceExponent rate F theta = 0 →
      queueLaplaceExponent rate F theta' = 0 →
      theta = theta' := by
  exact queueRootUniqueAux (queueLaplaceExponent rate F)
    (Kyprianou.Ch01.queueLaplaceExponent_strictConvex
      rate hrate F hpositive hfiniteMean mu hmu hmean)
    (Kyprianou.Ch01.queueLaplaceExponent_zero rate F)
