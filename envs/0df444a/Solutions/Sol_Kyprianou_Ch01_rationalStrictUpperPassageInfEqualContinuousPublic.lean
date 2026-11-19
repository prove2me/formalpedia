-- Prove2me | solution 1 for Kyprianou.Ch01.rationalStrictUpperPassageInfEqualContinuousPublic
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T12:38:44.040031+00:00
-- url     : https://prove2.me/submissions/1e7c845d-10f9-43c1-aa1a-8241e32a95cb

import Theorems.Thm_Kyprianou_Ch01_firstUpperPassage_le_rationalStrictInfPublic
import Theorems.Thm_Kyprianou_Ch01_rationalStrictInf_le_firstUpperPassageContinuousPublic
import Mathlib.Order.CompleteLattice.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.WithTop
import Mathlib.Data.NNReal.Defs
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Kyprianou.Ch01
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Rational crossing times are cofinal in the strict crossing set on continuous paths. -/
theorem solution
    {Ω : Type*} (X : ℝ≥0 → Ω → ℝ) (ω : Ω) (s : ℝ)
    (hContinuous : Continuous (fun t : ℝ≥0 => X t ω)) :
    firstUpperPassage X s ω =
      ⨅ r : ℚ,
        if (0 < (r : ℝ) ∧ s < X (Real.toNNReal (r : ℝ)) ω)
          then ((Real.toNNReal (r : ℝ)) : WithTop ℝ≥0)
          else ⊤ := by
  exact le_antisymm
    (firstUpperPassage_le_rationalStrictInfPublic X ω s)
    (rationalStrictInf_le_firstUpperPassageContinuousPublic X ω s hContinuous)
