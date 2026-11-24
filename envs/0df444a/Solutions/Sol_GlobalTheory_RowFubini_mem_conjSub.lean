-- Prove2me | solution 1 for GlobalTheory.RowFubini.mem_conjSub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:23:41.28154+00:00
-- url     : https://prove2.me/submissions/042004dd-70ec-4961-906c-0582a12eef78

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HaarTraceConjEqConstMulKernelImage

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped Pointwise ENNReal
open GlobalTheory GlobalTheory.RowFubini
variable {X : Type*} [Group X] [TopologicalSpace X] [IsTopologicalGroup X]
omit [TopologicalSpace X] [IsTopologicalGroup X]
namespace GlobalTheory.RowFubini
theorem _root_.solution (K : Subgroup X) (b x : X) : x ∈ conjSub K b ↔ b⁻¹ * x * b ∈ K := by
  simp [conjSub]
end GlobalTheory.RowFubini
