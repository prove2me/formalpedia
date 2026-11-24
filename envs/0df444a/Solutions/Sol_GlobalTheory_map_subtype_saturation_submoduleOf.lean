-- Prove2me | solution 1 for GlobalTheory.map_subtype_saturation_submoduleOf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:39:44.724465+00:00
-- url     : https://prove2.me/submissions/eed9a78c-bd98-435b-8005-3505a8c6b55b

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
theorem _root_.solution (M N : Submodule R V) :
    (saturation (N.submoduleOf M)).map M.subtype = saturationIn M N := by
  rw [map_subtype_saturation, Submodule.submoduleOf, Submodule.map_comap_subtype, saturationIn_inf]
end GlobalTheory
