-- Prove2me | solution 1 for Kyprianou.Ch01.measurable_eval_of_joint
-- status  : ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-24T17:05:59.375343+00:00
-- url     : https://prove2.me/submissions/ff3c3c40-1270-4dd6-b2ff-0fae40f21bbf

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (X : ℝ≥0 → Ω → ℤ)
    (hX : Measurable (fun p : Ω × ℝ≥0 => X p.2 p.1)) :
    ∀ t : ℝ≥0, Measurable (X t) := by
  intro t
  -- (ω ↦ (ω, t)) then jointly measurable evaluation
  exact hX.comp (measurable_id.prodMk measurable_const)
