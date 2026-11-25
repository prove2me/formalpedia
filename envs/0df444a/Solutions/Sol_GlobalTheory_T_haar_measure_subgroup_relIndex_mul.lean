-- Prove2me | solution 1 for GlobalTheory.T.haar_measure_subgroup_relIndex_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:24:32.241424+00:00
-- url     : https://prove2.me/submissions/61d54dcd-1768-427e-a65e-56e9200491c4

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HaarMeasureSubgroupRelIndexMul
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HaarMeasureSubgroupRelIndexMulStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_HaarIndex_measure_eq_relIndex_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped Topology
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (G : Type) [AddGroup G] [MeasurableSpace G] [MeasurableAdd G] (μ : MeasureTheory.Measure G) [μ.IsAddLeftInvariant] (H K : AddSubgroup G), H ≤ K → MeasurableSet (H : Set G) → H.relIndex K ≠ 0 → μ (K : Set G) = (H.relIndex K : ENNReal) * μ (H : Set G) := by
  first | exact @GlobalTheory.CompanionTheory.HaarIndex.measure_eq_relIndex_mul | exact GlobalTheory.CompanionTheory.HaarIndex.measure_eq_relIndex_mul | (intros; apply GlobalTheory.CompanionTheory.HaarIndex.measure_eq_relIndex_mul <;> assumption)
end _root_.GlobalTheory.T
