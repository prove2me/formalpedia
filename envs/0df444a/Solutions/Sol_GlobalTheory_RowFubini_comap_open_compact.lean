-- Prove2me | solution 1 for GlobalTheory.RowFubini.comap_open_compact
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:23:16.185254+00:00
-- url     : https://prove2.me/submissions/3f066674-f272-41cf-a52d-8757191c939a

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
namespace GlobalTheory.RowFubini
theorem _root_.solution (R Q : Subgroup X) (hR : IsClosed (R : Set X))
    (hQo : IsOpen (Q : Set X)) (hQc : IsCompact (Q : Set X)) :
    IsOpen ((Q.comap R.subtype : Subgroup R) : Set R) ∧
      IsCompact ((Q.comap R.subtype : Subgroup R) : Set R) :=
  ⟨hQo.preimage continuous_subtype_val, hR.isClosedEmbedding_subtypeVal.isCompact_preimage hQc⟩
end GlobalTheory.RowFubini
