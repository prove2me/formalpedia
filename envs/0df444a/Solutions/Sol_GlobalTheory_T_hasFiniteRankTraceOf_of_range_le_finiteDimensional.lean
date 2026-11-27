-- Prove2me | solution 1 for GlobalTheory.T.hasFiniteRankTraceOf_of_range_le_finiteDimensional
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T06:00:36.659533+00:00
-- url     : https://prove2.me/submissions/bb50d02f-9144-483a-9cf8-34f23e81924f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasFiniteRankTraceOfOfRangeLeFiniteDimensional
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_IwahoriDoubleCosets
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasFiniteRankTraceOfOfRangeLeFiniteDimensionalStatement
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_RangeTrace_hasFinTrace_of_range_le


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (X : Type) [AddCommGroup X] [Module ℂ X] (T : X →ₗ[ℂ] X) (Z : Submodule ℂ X)
    [FiniteDimensional ℂ Z] (hT : LinearMap.range T ≤ Z),
    GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.HasFinTrace T (LinearMap.trace ℂ Z (T.restrict (p := Z) (q := Z)
      fun x _ => hT (LinearMap.mem_range_self T x))) := by
  first | exact @GlobalTheory.IndefiniteRowSideFullHecke.RangeTrace.hasFinTrace_of_range_le | exact GlobalTheory.IndefiniteRowSideFullHecke.RangeTrace.hasFinTrace_of_range_le | (intros; apply GlobalTheory.IndefiniteRowSideFullHecke.RangeTrace.hasFinTrace_of_range_le <;> assumption)
end _root_.GlobalTheory.T
