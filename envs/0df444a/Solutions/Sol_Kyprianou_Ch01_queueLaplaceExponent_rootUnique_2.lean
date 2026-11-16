-- Prove2me | solution 2 for Kyprianou.Ch01.queueLaplaceExponent_rootUnique
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T10:33:22.942489+00:00
-- url     : https://prove2.me/submissions/0fde25cc-e555-4cdb-af11-381648f7d1c6

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

/-- A strictly convex function vanishing at zero has at most one positive root. -/
theorem solution
    (rate : ℝ≥0) (hrate : 0 < rate)
    (F : Measure ℝ) [IsProbabilityMeasure F]
    (hpositive : F (Set.Iic (0 : ℝ)) = 0)
    (hfiniteMean : Integrable (fun x : ℝ => x) F)
    (mu : ℝ) (hmu : 0 < mu)
    (hmean : (∫ x, x ∂F) = mu) :
    (∀ theta theta' : ℝ,
      0 < theta → 0 < theta' →
      queueLaplaceExponent rate F theta = 0 →
      queueLaplaceExponent rate F theta' = 0 →
      theta = theta') := by
  let f := queueLaplaceExponent rate F
  have hc : StrictConvexOn ℝ (Set.Ici (0 : ℝ)) f :=
    Kyprianou.Ch01.queueLaplaceExponent_strictConvex
      rate hrate F hpositive hfiniteMean mu hmu hmean
  have hz : f 0 = 0 :=
    Kyprianou.Ch01.queueLaplaceExponent_zero rate F
  have hcontra (u v : ℝ) (hu : 0 < u) (huv : u < v)
      (hfu : f u = 0) (hfv : f v = 0) : False := by
    let b : ℝ := u / v
    let a : ℝ := 1 - b
    have hv : 0 < v := lt_trans hu huv
    have hb : 0 < b := div_pos hu hv
    have hb1 : b < 1 := (div_lt_one hv).2 huv
    have ha : 0 < a := by dsimp [a]; linarith
    have hab : a + b = 1 := by dsimp [a]; ring
    have hcv := hc.2 (show (0 : ℝ) ∈ Set.Ici 0 by simp)
      (show v ∈ Set.Ici 0 by exact le_of_lt hv)
      (ne_of_lt hv) ha hb hab
    have hbu : b * v = u := by
      dsimp [b]
      field_simp
    have hcoord : a • (0 : ℝ) + b • v = u := by
      simpa only [smul_eq_mul, mul_zero, zero_add] using hbu
    rw [hcoord, hz, hfv, hfu] at hcv
    norm_num at hcv
  intro theta theta' hθ hθ' hfθ hfθ'
  rcases lt_trichotomy theta theta' with hlt | heq | hgt
  · exact False.elim (hcontra theta theta' hθ hlt hfθ hfθ')
  · exact heq
  · exact False.elim (hcontra theta' theta hθ' hgt hfθ' hfθ)
