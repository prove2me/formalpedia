-- Prove2me | solution 1 for GlobalTheory.AvgSmooth.integrable_cont
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:23:47.501152+00:00
-- url     : https://prove2.me/submissions/44adb0bc-f2a0-4a0b-83cb-433d1340028e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ContDiffCompactAverageOfClosedPartials

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped ContDiff
noncomputable section
open GlobalTheory GlobalTheory.AvgSmooth
variable {K : Type} [TopologicalSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K] {n : ℕ}
namespace GlobalTheory.AvgSmooth
theorem _root_.solution (μ : Measure K) [IsFiniteMeasure μ] {f : K → ℂ} (hf : Continuous f) : Integrable f μ := by
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hf.continuousOn
  exact Integrable.of_bound hf.aestronglyMeasurable C (Filter.Eventually.of_forall fun k => hC k (Set.mem_univ k))
end GlobalTheory.AvgSmooth
