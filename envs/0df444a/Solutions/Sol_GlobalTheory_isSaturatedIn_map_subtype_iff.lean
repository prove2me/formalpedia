-- Prove2me | solution 1 for GlobalTheory.isSaturatedIn_map_subtype_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:39:05.403155+00:00
-- url     : https://prove2.me/submissions/8c3771ad-de27-4be9-b1ae-487e0a464f70

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_MemSaturatedOrderIsoSubspaceSpanSymmApply
import Theorems.Thm_GlobalTheory_map_subtype_saturation

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped nonZeroDivisors Pointwise
open GlobalTheory
variable {R : Type*} [CommRing R] {V V' : Type*} [AddCommGroup V] [Module R V]
  [AddCommGroup V'] [Module R V']
namespace GlobalTheory
theorem _root_.solution {M : Submodule R V} {N : Submodule R M} :
    IsSaturatedIn M (N.map M.subtype) ↔ IsSaturatedSubmodule N := by
  unfold IsSaturatedIn IsSaturatedSubmodule
  rw [← map_subtype_saturation]
  exact (Submodule.map_injective_of_injective (f := M.subtype) Subtype.coe_injective).eq_iff
end GlobalTheory
