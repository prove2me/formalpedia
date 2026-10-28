-- Prove2me | solution 1 for OAI.ReusedScalar205.CubicTorus.Scalar.baseline_chord_lower
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T19:49:32.235633+00:00
-- url     : https://prove2.me/submissions/d9db3dee-64fe-4379-80a7-bfa760764382

import Mathlib
import Definitions.Def_OAIQ079A003
import Theorems.Thm_OAI_ReusedScalar205_CubicTorus_Scalar_concaveOn_baseline_corrected

section
-- module Solutions.OAIQ079_CT.CubicTorus_Profiles_GainBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace ReusedScalar205
noncomputable section
noncomputable section
open Set MeasureTheory
open scoped ENNReal
noncomputable section
open Set MeasureTheory
open scoped Interval

namespace CubicTorus.Scalar
open Set _root_.OAI.ReusedScalar205.CubicTorus.Nesting _root_.OAI.ReusedScalar205.CubicTorus.Shape

lemma semiconcave_chord_bound {f : ℝ → ℝ} {a b c x : ℝ} (hab : a < b) (hc : 0 ≤ c)
    (hf : ConcaveOn ℝ (Icc a b) (fun y ↦ f y - c * y ^ 2)) (hx : x ∈ Icc a b) :
    min (f a) (f b) - c * (b - a) ^ 2 / 4 ≤ f x := by
  let w := (b - x) / (b - a)
  let v := (x - a) / (b - a)
  have hd : 0 < b - a := sub_pos.2 hab
  have hw : 0 ≤ w := div_nonneg (sub_nonneg.2 hx.2) hd.le
  have hv : 0 ≤ v := div_nonneg (sub_nonneg.2 hx.1) hd.le
  have hsum : w + v = 1 := by dsimp [w, v]; field_simp; ring
  have harg : w * a + v * b = x := by dsimp [w, v]; field_simp; ring
  have hcon := hf.2 (left_mem_Icc.2 hab.le) (right_mem_Icc.2 hab.le) hw hv hsum
  simp only [smul_eq_mul, harg] at hcon
  have hmin : min (f a) (f b) ≤ w * f a + v * f b := by
    have ha := mul_le_mul_of_nonneg_left (min_le_left (f a) (f b)) hw
    have hb := mul_le_mul_of_nonneg_left (min_le_right (f a) (f b)) hv
    calc
      _ = w * min (f a) (f b) + v * min (f a) (f b) := by rw [← add_mul, hsum, one_mul]
      _ ≤ _ := add_le_add ha hb
  have hcorr : w * c * a ^ 2 + v * c * b ^ 2 - c * x ^ 2 = c * (x - a) * (b - x) := by
    dsimp [w, v]
    field_simp
    ring
  have hprod : (x - a) * (b - x) ≤ (b - a) ^ 2 / 4 := by nlinarith [sq_nonneg (2 * x - a - b)]
  have hprod' := mul_le_mul_of_nonneg_left hprod hc
  nlinarith only [hcon, hmin, hcorr, hprod']

lemma baseline_chord_lower_oai {a b x l r : ℝ} (ha : 0 < a) (hab : a < b)
    (hx : x ∈ Icc a b) (hl : l ≤ baseline a) (hr : r ≤ baseline b) :
    min l r - (b - a) ^ 2 / (4 * a ^ 2) ≤ baseline x := by
  have hf : ConcaveOn ℝ (Icc a b) (fun y ↦ baseline y - (1 / a ^ 2) * y ^ 2) := by
    convert concaveOn_baseline_corrected (b := b) ha using 1
    all_goals try with_reducible_and_instances rfl
    funext y
    ring
  have hbound := semiconcave_chord_bound hab (by positivity : 0 ≤ (1 : ℝ) / a ^ 2) hf hx
  have hmin := min_le_min hl hr
  have heq : (b - a) ^ 2 / (4 * a ^ 2) = (1 / a ^ 2) * (b - a) ^ 2 / 4 := by ring
  rw [heq]
  linarith

end CubicTorus.Scalar

end
end
end
end ReusedScalar205
end
end

end OAI
end

theorem solution : type_of% @OAI.ReusedScalar205.CubicTorus.Scalar.baseline_chord_lower_oai := @OAI.ReusedScalar205.CubicTorus.Scalar.baseline_chord_lower_oai
