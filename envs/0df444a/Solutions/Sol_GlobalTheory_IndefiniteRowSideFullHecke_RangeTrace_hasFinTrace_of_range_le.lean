-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.RangeTrace.hasFinTrace_of_range_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:57:28.126777+00:00
-- url     : https://prove2.me/submissions/c2b84077-1b3a-4aec-b167-a190845ab9ee

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_IwahoriDoubleCosets
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasFiniteRankTraceOfOfRangeLeFiniteDimensional

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.RangeTrace
namespace GlobalTheory.IndefiniteRowSideFullHecke.RangeTrace
theorem _root_.solution (X : Type) [AddCommGroup X] [Module ℂ X] (T : X →ₗ[ℂ] X)
    (Z : Submodule ℂ X) [FiniteDimensional ℂ Z] (hT : LinearMap.range T ≤ Z) :
    GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.HasFinTrace T (LinearMap.trace ℂ Z (T.restrict (p := Z) (q := Z)
      fun x _ => hT (LinearMap.mem_range_self T x))) := by
  haveI : FiniteDimensional ℂ (LinearMap.range T) := Submodule.finiteDimensional_of_le hT
  refine ⟨inferInstance, ?_⟩
  have hmem : ∀ x : Z, (T.restrict (p := Z) (q := Z)
      fun x _ => hT (LinearMap.mem_range_self T x)) x ∈ (LinearMap.range T).comap Z.subtype :=
    fun x => LinearMap.mem_range_self T (x : X)
  rw [← LinearMap.trace_restrict_eq_of_forall_mem _ _ hmem,
    ← LinearMap.trace_conj' _ (Submodule.comapSubtypeEquivOfLe hT)]
  congr 1
end GlobalTheory.IndefiniteRowSideFullHecke.RangeTrace
