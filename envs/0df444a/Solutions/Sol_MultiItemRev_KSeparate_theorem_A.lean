-- Prove2me | solution 1 for MultiItemRev.KSeparate.theorem_A
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T16:16:13.178207+00:00
-- url     : https://prove2.me/submissions/f1011184-84e4-48c2-b18d-8df952a3cf5a

import Mathlib
import Definitions.Def_MultiItemRev_KSeparate_Model
import Theorems.Thm_MultiItemRev_KSeparate_theorem_7

open MeasureTheory
open scoped NNReal ENNReal

theorem solution (ν₁ ν₂ : Measure ℝ≥0)
    [IsProbabilityMeasure ν₁] [IsProbabilityMeasure ν₂] :
    MultiItemRev.Decomp.Rev (MultiItemRev.Decomp.jointLaw (MultiItemRev.Decomp.oneGood ν₁) (MultiItemRev.Decomp.oneGood ν₂)) ≤
      2 * (MultiItemRev.Decomp.Rev1 ν₁ + MultiItemRev.Decomp.Rev1 ν₂) := by
  haveI : IsProbabilityMeasure (MultiItemRev.Decomp.oneGood ν₁) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  haveI : IsProbabilityMeasure (MultiItemRev.Decomp.oneGood ν₂) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  have h := MultiItemRev.KSeparate.theorem_7 (MultiItemRev.Decomp.oneGood ν₁)
    (MultiItemRev.Decomp.oneGood ν₂)
  exact h.1.trans h.2
