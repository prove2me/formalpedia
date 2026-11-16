-- Prove2me | solution 1 for Kyprianou.Ch01.queueLaplaceExponentStrictConvexAndRoot
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T19:30:50.673484+00:00
-- url     : https://prove2.me/submissions/e49145b7-68e1-4d68-acb4-d0d6d8932e8e

import Mathlib
import Definitions.Def_Kyprianou_Ch01_RiskQueueCore
import Theorems.Thm_Kyprianou_Ch01_queueLaplaceExponent_strictConvex
import Theorems.Thm_Kyprianou_Ch01_queueLaplaceExponent_diverges
import Theorems.Thm_Kyprianou_Ch01_queueLaplaceExponent_rootIff
import Theorems.Thm_Kyprianou_Ch01_queueLaplaceExponent_rootUnique
import Theorems.Thm_Kyprianou_Ch01_queueLaplaceExponent_zero
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    (rate : ℝ≥0) (hrate : 0 < rate)
    (F : Measure ℝ) [IsProbabilityMeasure F]
    (hpositive : F (Set.Iic (0 : ℝ)) = 0)
    (hfiniteMean : Integrable (fun x : ℝ => x) F)
    (mu : ℝ) (hmu : 0 < mu)
    (hmean : (∫ x, x ∂F) = mu) :
    StrictConvexOn ℝ (Set.Ici (0 : ℝ))
      (queueLaplaceExponent rate F) ∧
    queueLaplaceExponent rate F 0 = 0 ∧
    Tendsto (queueLaplaceExponent rate F) atTop atTop ∧
    ((∃ theta : ℝ, 0 < theta ∧
      queueLaplaceExponent rate F theta = 0) ↔
        1 < (rate : ℝ) * mu) ∧
    (∀ theta theta' : ℝ,
      0 < theta → 0 < theta' →
      queueLaplaceExponent rate F theta = 0 →
      queueLaplaceExponent rate F theta' = 0 →
      theta = theta') := by
  refine ⟨
    Kyprianou.Ch01.queueLaplaceExponent_strictConvex rate hrate F hpositive
      hfiniteMean mu hmu hmean,
    Kyprianou.Ch01.queueLaplaceExponent_zero rate F,
    Kyprianou.Ch01.queueLaplaceExponent_diverges rate hrate F hpositive
      hfiniteMean mu hmu hmean,
    Kyprianou.Ch01.queueLaplaceExponent_rootIff rate hrate F hpositive
      hfiniteMean mu hmu hmean,
    Kyprianou.Ch01.queueLaplaceExponent_rootUnique rate hrate F hpositive
      hfiniteMean mu hmu hmean⟩
