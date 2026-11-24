-- Prove2me | solution 1 for GlobalTheory.map_saturation_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:19:48.873804+00:00
-- url     : https://prove2.me/submissions/0ffbcf1a-30a5-4049-a045-2a152443a563

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
variable {R : Type*} [CommRing R] {M M' : Type*} [AddCommGroup M] [Module R M]
  [AddCommGroup M'] [Module R M']
namespace GlobalTheory
theorem _root_.solution (f : M →ₗ[R] M') (N : Submodule R M) :
    (saturation N).map f ≤ saturation (N.map f) := by
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨a, ha, hax⟩ := mem_saturation_iff'.1 hx
  refine mem_saturation_iff'.2 ⟨a, ha, ?_⟩
  rw [← map_smul]
  exact Submodule.mem_map_of_mem hax
end GlobalTheory
