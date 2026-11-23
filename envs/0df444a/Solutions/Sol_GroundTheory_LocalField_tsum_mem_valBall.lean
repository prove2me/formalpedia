-- Prove2me | solution 1 for GroundTheory.LocalField.tsum_mem_valBall
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:24:33.399929+00:00
-- url     : https://prove2.me/submissions/1d764360-8c06-450c-bac2-58535222c801

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_ExistsUnitFiltrationUnitsLeAndRangePowLe
import Definitions.Def_GroundTheory_LocalFields_ExamplesCharZero
import Definitions.Def_GroundTheory_LocalFields_PadicLogSeries
import Theorems.Thm_GroundTheory_LocalField_isClosed_valBall

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.LocalField
open ValuativeRel IsLocalRing Topology Filter
open scoped WithZero
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
namespace GroundTheory.LocalField
theorem _root_.solution {f : ℕ → K} {N : ℤ} (h : ∀ k, f k ∈ valBall K N) :
    ∑' k, f k ∈ valBall K N := by
  by_cases hs : Summable f
  · exact (isClosed_valBall N).mem_of_tendsto hs.hasSum.tendsto_sum_nat
      (Eventually.of_forall fun s ↦ AddSubgroup.sum_mem _ fun k _ ↦ h k)
  · rw [tsum_eq_zero_of_not_summable hs]
    exact zero_mem _
end GroundTheory.LocalField
