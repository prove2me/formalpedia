-- Prove2me | solution 2 for GlobalTheory.map_subtype_saturation
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:33:49.429855+00:00
-- url     : https://prove2.me/submissions/535ec6d1-cad5-4790-84f5-0321c85337dd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_MemSaturatedOrderIsoSubspaceSpanSymmApply
import Theorems.Thm_GlobalTheory_map_saturation_of_injective

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
theorem _root_.solution (M : Submodule R V) (N : Submodule R M) :
    (saturation N).map M.subtype = saturationIn M (N.map M.subtype) := by
  rw [map_saturation_of_injective (f := M.subtype) Subtype.coe_injective, Submodule.range_subtype,
    saturationIn_def]
end GlobalTheory
