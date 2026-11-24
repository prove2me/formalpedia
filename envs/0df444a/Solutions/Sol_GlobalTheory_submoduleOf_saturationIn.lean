-- Prove2me | solution 1 for GlobalTheory.submoduleOf_saturationIn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:35:29.741576+00:00
-- url     : https://prove2.me/submissions/93848e5d-eef8-4cbe-8a4d-cf1dba1aad6a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_MemSaturatedOrderIsoSubspaceSpanSymmApply

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
    (saturationIn M N).submoduleOf M = saturation (N.submoduleOf M) := by
  rw [saturationIn_def, Submodule.submoduleOf, Submodule.submoduleOf, Submodule.comap_inf,
    saturation_comap, Submodule.comap_subtype_self, top_inf_eq]
end GlobalTheory
