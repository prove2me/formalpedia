-- Prove2me | solution 1 for GroundTheory.ProfCoh.exact_connecting_modNMap
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:02:40.823245+00:00
-- url     : https://prove2.me/submissions/8c0c386e-470d-4b2f-8f8e-dc2b83782fd4

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_AdditiveDefs
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_AdditiveSnake
import Theorems.Thm_GroundTheory_ProfCoh_modN_mk_eq_zero_iff
import Theorems.Thm_GroundTheory_ProfCoh_connecting_spec
import Theorems.Thm_GroundTheory_ProfCoh_coe_torsNRep_apply
import Theorems.Thm_GroundTheory_ProfCoh_modNRep_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.ProfCoh.coe_torsNRep_apply
attribute [local simp] GroundTheory.ProfCoh.modNRep_mk



set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.ProfCoh
universe u v
open Representation
variable {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] (n : ℕ)
variable {n} (f : A →+ B) (h : B →+ C) (hh : Function.Surjective h)
variable {f h}
variable (hfh : Function.Exact f h)
include hh hfh
variable (hf : Function.Injective f)
include hf
namespace GroundTheory.ProfCoh
theorem _root_.solution : Function.Exact (connecting hh hfh hf) (modNMap n f) := by
  intro q
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  rw [modNMap_mk, modN_mk_eq_zero_iff]
  constructor
  · rintro ⟨b, hb⟩
    have hc : h b ∈ LinearMap.ker (LinearMap.lsmul ℤ C (n : ℤ)) := by
      rw [mem_ker_lsmul_iff, ← map_nsmul, hb]
      exact (hfh _).2 ⟨a, rfl⟩
    exact ⟨⟨h b, hc⟩, connecting_spec hh hfh hf _ b a rfl hb.symm⟩
  · rintro ⟨c, hc⟩
    obtain ⟨b, a', hb, ha'⟩ := exists_lift hh hfh c
    rw [connecting_spec hh hfh hf c b a' hb ha', Submodule.Quotient.eq] at hc
    obtain ⟨y, hy⟩ := hc
    refine ⟨b - f y, ?_⟩
    simp only [LinearMap.lsmul_apply, natCast_zsmul] at hy
    rw [smul_sub, ← ha', ← map_nsmul, ← map_sub, hy, sub_sub_cancel]
end GroundTheory.ProfCoh
