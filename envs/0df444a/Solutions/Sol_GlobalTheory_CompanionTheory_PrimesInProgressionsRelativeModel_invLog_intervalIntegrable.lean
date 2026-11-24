-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.PrimesInProgressionsRelativeModel.invLog_intervalIntegrable
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:17:19.664582+00:00
-- url     : https://prove2.me/submissions/9dcd0615-450f-4306-89df-35c81ab185f0

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_PublishedTheorems_PublishedGlobalResults_PrimesInProgressionsRelative
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_PrimesInProgressionsRelativeOfTzRat
import Definitions.Def_Development_AutomorphicSpectrum_PublishedTheorems_PublishedGlobalResults_InvLogIntervalIntegrable

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators Classical
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.PrimesInProgressionsRelativeModel
namespace GlobalTheory.CompanionTheory.PrimesInProgressionsRelativeModel
theorem _root_.solution {u v : ℝ} (hu : 2 ≤ u) (hv : 2 ≤ v) :
    IntervalIntegrable (fun t : ℝ => 1 / Real.log t) MeasureTheory.volume u v := by
  apply ContinuousOn.intervalIntegrable
  have h2 : ∀ t ∈ Set.uIcc u v, (2 : ℝ) ≤ t := fun t ht => le_trans (le_min hu hv) ht.1
  refine ContinuousOn.div continuousOn_const (Real.continuousOn_log.mono ?_) ?_
  · intro t ht; have := h2 t ht; simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; linarith
  · intro t ht; have := h2 t ht; exact (Real.log_pos (by linarith)).ne'
end GlobalTheory.CompanionTheory.PrimesInProgressionsRelativeModel
