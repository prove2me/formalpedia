-- Prove2me | solution 1 for MultiItemRev.KSeparate.myerson_one_good
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T16:14:07.476203+00:00
-- url     : https://prove2.me/submissions/2652c08a-54da-45b2-a255-7b5a531d5151

import Mathlib
import Definitions.Def_MultiItemRev_KSeparate_Model
import Theorems.Thm_MultiItemRev_KBundling_myerson_one_good

open MeasureTheory
open scoped NNReal ENNReal

theorem solution (ν : Measure ℝ≥0) [IsProbabilityMeasure ν] :
    MultiItemRev.Decomp.Rev1 ν = ⨆ p : ℝ≥0, (p : ℝ≥0∞) * ν {t | p ≤ t} ∧
    MultiItemRev.Decomp.Rev1 ν = ⨆ p : ℝ≥0, (p : ℝ≥0∞) * ν {t | p < t} ∧
    MultiItemRev.Decomp.Rev1 ν = ⨆ p : ℝ≥0, (p : ℝ≥0∞) * (1 - ν {t | t ≤ p}) :=
  MultiItemRev.KBundling.myerson_one_good ν
