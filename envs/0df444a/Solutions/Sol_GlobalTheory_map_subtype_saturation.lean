-- Prove2me | solution 1 for GlobalTheory.map_subtype_saturation
-- status  : ACCEPTED   (prove)
-- author  : @sockpaprika
-- created : 2026-11-24T04:52:44.94066+00:00
-- url     : https://prove2.me/submissions/84eee9ac-44f1-4c55-97c4-61c0f11683d7

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
private theorem sat_map_aux {f : M →ₗ[R] M'} (hf : Function.Injective f)
    (N : Submodule R M) :
    (saturation N).map f = LinearMap.range f ⊓ saturation (N.map f) := by
  ext y; constructor
  · rintro ⟨x,hx,rfl⟩
    obtain ⟨a,ha,hax⟩ := mem_saturation_iff'.mp hx
    exact ⟨⟨x,rfl⟩,mem_saturation_iff'.mpr ⟨a,ha,a • x,hax,f.map_smul a x⟩⟩
  · rintro ⟨⟨x,rfl⟩,hs⟩
    obtain ⟨a,ha,z,hz,he⟩ := mem_saturation_iff'.mp hs
    have he' : z = a • x := hf (he.trans (f.map_smul a x).symm)
    exact ⟨x,mem_saturation_iff'.mpr ⟨a,ha,he' ▸ hz⟩,rfl⟩
variable {V : Type*} [AddCommGroup V] [Module R V]



theorem solution (M : Submodule R V) (N : Submodule R M) :
    (saturation N).map M.subtype = saturationIn M (N.map M.subtype) := by
  simpa [saturationIn_def] using sat_map_aux (f := M.subtype) Subtype.val_injective N
