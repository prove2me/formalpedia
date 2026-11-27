-- Prove2me | solution 1 for GlobalTheory.map_saturationIn_of_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:40:06.369463+00:00
-- url     : https://prove2.me/submissions/32baf7c2-359a-453c-bbc8-a99d95eb1ef4

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
theorem _root_.solution {f : V →ₗ[R] V'} (hf : Function.Injective f)
    (M N : Submodule R V) :
    (saturationIn M N).map f = saturationIn (M.map f) (N.map f) := by
  rw [saturationIn_def, saturationIn_def, Submodule.map_inf f hf, map_saturation_of_injective hf,
    ← inf_assoc, inf_of_le_left LinearMap.map_le_range]
end GlobalTheory
