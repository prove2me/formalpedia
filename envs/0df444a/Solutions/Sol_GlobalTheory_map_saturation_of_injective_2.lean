-- Prove2me | solution 2 for GlobalTheory.map_saturation_of_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:26:59.343492+00:00
-- url     : https://prove2.me/submissions/50f47539-f6b6-4047-b1ed-738b5f499f08

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_MemSaturatedOrderIsoSubspaceSpanSymmApply
import Theorems.Thm_GlobalTheory_map_saturation_le

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
theorem _root_.solution {f : M →ₗ[R] M'} (hf : Function.Injective f)
    (N : Submodule R M) :
    (saturation N).map f = LinearMap.range f ⊓ saturation (N.map f) := by
  refine le_antisymm (le_inf LinearMap.map_le_range (map_saturation_le f N)) ?_
  intro y hy
  obtain ⟨hr, hs⟩ := Submodule.mem_inf.1 hy
  obtain ⟨x, rfl⟩ := LinearMap.mem_range.1 hr
  obtain ⟨a, ha, hmem⟩ := mem_saturation_iff'.1 hs
  obtain ⟨n, hn, hfn⟩ := Submodule.mem_map.1 hmem
  refine Submodule.mem_map_of_mem (mem_saturation_iff'.2 ⟨a, ha, ?_⟩)
  rw [← map_smul] at hfn
  rw [← hf hfn]
  exact hn
end GlobalTheory
