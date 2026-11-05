-- Prove2me | solution 1 for MultiItemRev.TwoIID.myerson_one_good
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T15:49:54.73543+00:00
-- url     : https://prove2.me/submissions/3661b3c6-5e76-4f70-9cbd-5381d5b42143

import Mathlib
import Definitions.Def_MultiItemRev_TwoIID_Model
import Theorems.Thm_MultiItemRev_KBundling_myerson_one_good

open MeasureTheory
open scoped NNReal ENNReal

theorem solution (ν : Measure ℝ≥0) [IsProbabilityMeasure ν] :
    MultiItemRev.Decomp.Rev1 ν = ⨆ p : ℝ≥0, (p : ℝ≥0∞) * ν {t | p ≤ t} ∧
    MultiItemRev.Decomp.Rev1 ν = ⨆ p : ℝ≥0, (p : ℝ≥0∞) * ν {t | p < t} :=
  ⟨(MultiItemRev.KBundling.myerson_one_good ν).1, (MultiItemRev.KBundling.myerson_one_good ν).2.1⟩
