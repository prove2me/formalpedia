-- Prove2me | solution 1 for NestedSeatAlloc.IntPolicy.condRevenue_one_concave_nonneg_fare
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T16:39:12.399387+00:00
-- url     : https://prove2.me/submissions/02dd39dd-f70b-4a43-8c35-2909ea917343

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
import Theorems.Thm_NestedSeatAlloc_IntPolicy_condRevenue_one_frozen_formula

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory NestedSeatAlloc.IntPolicy

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → Ω → ℝ) (f p : ℕ → ℝ)
    (hM : IsSeatModel P X f) (hf1 : 0 ≤ f 1) (y : ℝ) :
    ConcaveOn ℝ (Set.Ici 0)
      (condRevenue P X f p 1 y) := by
  have hfun : (condRevenue P X f p 1 y) =
      (fun s : ℝ => f 1 * min s y) := by
    funext s
    rw [condRevenue_one_frozen_formula P X f p hM.isProb y s]
    by_cases hs : s < y
    · simp [hs, min_eq_left (le_of_lt hs)]
    · simp [hs, min_eq_right (le_of_not_gt hs)]
  rw [hfun]
  refine ⟨(convex_Ici (0 : ℝ)), ?_⟩
  intro x hx z hz a c ha hc hac
  simp only [smul_eq_mul]
  have hmin : a * min x y + c * min z y ≤
      min (a * x + c * z) y := by
    apply le_min
    · have hxle : min x y ≤ x := min_le_left _ _
      have hzle : min z y ≤ z := min_le_left _ _
      nlinarith [mul_nonneg ha (sub_nonneg.mpr hxle),
        mul_nonneg hc (sub_nonneg.mpr hzle)]
    · have hxle : min x y ≤ y := min_le_right _ _
      have hzle : min z y ≤ y := min_le_right _ _
      calc
        a * min x y + c * min z y ≤ a * y + c * y :=
          add_le_add
            (mul_le_mul_of_nonneg_left hxle ha)
            (mul_le_mul_of_nonneg_left hzle hc)
        _ = y := by rw [← add_mul, hac, one_mul]
  calc
    a * (f 1 * min x y) + c * (f 1 * min z y) =
        f 1 * (a * min x y + c * min z y) := by ring
    _ ≤ f 1 * min (a * x + c * z) y :=
      mul_le_mul_of_nonneg_left hmin hf1
