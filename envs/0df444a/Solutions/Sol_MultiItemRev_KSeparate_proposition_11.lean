-- Prove2me | solution 1 for MultiItemRev.KSeparate.proposition_11
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T16:16:13.973073+00:00
-- url     : https://prove2.me/submissions/d3cee1f8-2038-4921-a67b-d48467b9c2dc

import Mathlib
import Definitions.Def_MultiItemRev_KSeparate_Model
import Theorems.Thm_MultiItemRev_KSeparate_myerson_one_good

open MeasureTheory
open scoped NNReal ENNReal

open MultiItemRev.KSeparate in
theorem solution (ν ν' : Measure ℝ≥0)
    [IsProbabilityMeasure ν] [IsProbabilityMeasure ν']
    (h : StochDominated ν ν') : MultiItemRev.Decomp.Rev1 ν ≤ MultiItemRev.Decomp.Rev1 ν' := by
  rw [(myerson_one_good ν).1, (myerson_one_good ν').1]
  exact iSup_mono fun p => mul_le_mul_of_nonneg_left (h p) zero_le
