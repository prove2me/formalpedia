-- Prove2me | solution 1 for Kyprianou.Ch02.nonnegLaplaceFactorIndepFunV1
-- status  : ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-24T02:41:34.553439+00:00
-- url     : https://prove2.me/submissions/f3cfc88a-6883-4494-8fd7-91b57904c29d

import Theorems.Thm_AvramDividend_Classical_avram_ws01e_bi_new_nonneg_upperray_restricted_laplace_indepFun
import Theorems.Thm_Kyprianou_Ch02_nonnegLaplaceProductUpperRayFactorV1
import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false
set_option linter.unusedVariables false

/-!
Nonnegative measurable joint Laplace product ⇒ IndepFun:
apply the proved Avram upper-ray Laplace criterion, discharging its
restricted-factor hypothesis via `nonnegLaplaceProductUpperRayFactorV1`.
-/

theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (A B : Ω → ℝ) (hmA : Measurable A) (hmB : Measurable B)
    (hnA : ∀ ω, 0 ≤ A ω) (hnB : ∀ ω, 0 ≤ B ω)
    (h : ∀ u v : ℝ, 0 < u → 0 < v →
      (∫ ω, Real.exp (-(u * A ω + v * B ω)) ∂P) =
      (∫ ω, Real.exp (-(u * A ω)) ∂P) * (∫ ω, Real.exp (-(v * B ω)) ∂P)) :
    IndepFun A B P :=
  AvramDividend.Classical.avram_ws01e_bi_new_nonneg_upperray_restricted_laplace_indepFun
    P A B hmA hmB hnA hnB fun a β ha hβ =>
      Kyprianou.Ch02.nonnegLaplaceProductUpperRayFactorV1
        P A B hmA hmB hnA hnB h a β ha hβ
