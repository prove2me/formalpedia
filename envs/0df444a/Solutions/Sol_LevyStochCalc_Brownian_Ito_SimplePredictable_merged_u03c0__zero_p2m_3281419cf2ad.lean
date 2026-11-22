-- Prove2me | solution 1 for LevyStochCalc.Brownian.Ito.SimplePredictable.merged_u03c0__zero_p2m_3281419cf2ad
-- status  : ACCEPTED   (prove)
-- author  : @yuzhou
-- created : 2026-11-21T14:01:08.414647+00:00
-- url     : https://prove2.me/submissions/36a028fb-7e00-4409-b949-b5e0e9d73dec

import Definitions.Def_LevyStochCalc_Brownian_SimplePredictableRefineCommon_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Common refinement of two simple predictables and the difference isometry

The common refinement of two `SimplePredictable Ω T` sharing an endpoint: the
merged set of partition points, the merged partition `SimplePredictable.mergedπ`
with its two refining index maps, the induced refinements
`SimplePredictable.commonRefinement_left`/`_right` and their difference
`SimplePredictable.sub_on_common`. These give the difference isometry for simple
integrals (`SimplePredictable.diff_isometry_simple`) and the Cauchy property of
the simple integrals of an `L²`-Cauchy sequence of simple predictables
(`cauchy_of_L2_dense_simple`).
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory
open scoped NNReal ENNReal

universe u
variable {Ω : Type u} [MeasurableSpace Ω]



theorem _root_.solution
    {T : ℝ} (H₁ H₂ : SimplePredictable Ω T) :
    H₁.mergedπ H₂ 0 = 0 := by
  classical
  let S := H₁.mergedPartitionPoints H₂
  let e := S.orderEmbOfFin (H₁.mergedM_card_eq H₂)
  change e 0 = 0
  have hm : e 0 ∈ S := Finset.orderEmbOfFin_mem _ _ _
  have h0 : (0 : ℝ) ∈ S := H₁.zero_mem_mergedPartitionPoints H₂
  have hsurj : (0 : ℝ) ∈ Set.range e := by
    simpa [e, Finset.range_orderEmbOfFin] using h0
  obtain ⟨i, hi⟩ := hsurj
  exact le_antisymm ((e.monotone (Fin.zero_le i)).trans_eq hi)
    (H₁.mem_mergedPartitionPoints_nonneg H₂ hm)
