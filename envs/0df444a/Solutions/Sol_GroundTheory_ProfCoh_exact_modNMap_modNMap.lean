-- Prove2me | solution 1 for GroundTheory.ProfCoh.exact_modNMap_modNMap
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:03:04.67555+00:00
-- url     : https://prove2.me/submissions/25174d19-85c1-458e-a60e-c5d7f8d1bc54

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_AdditiveDefs
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_AdditiveSnake
import Theorems.Thm_GroundTheory_ProfCoh_modN_mk_eq_zero_iff
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
omit hf
namespace GroundTheory.ProfCoh
theorem _root_.solution : Function.Exact (modNMap n f) (modNMap n h) := by
  intro q
  obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  rw [modNMap_mk, modN_mk_eq_zero_iff]
  constructor
  · rintro ⟨c, hc⟩
    obtain ⟨b', rfl⟩ := hh c
    obtain ⟨a, ha⟩ := (hfh (b - n • b')).1 (by rw [map_sub, map_nsmul, hc, sub_self])
    refine ⟨Submodule.Quotient.mk a, ?_⟩
    rw [modNMap_mk, ha, Submodule.Quotient.eq]
    exact ⟨-b', by simp⟩
  · rintro ⟨q', hq'⟩
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ q'
    rw [modNMap_mk, Submodule.Quotient.eq] at hq'
    obtain ⟨y, hy⟩ := hq'
    simp only [LinearMap.lsmul_apply, natCast_zsmul] at hy
    refine ⟨-h y, ?_⟩
    rw [smul_neg, ← map_nsmul, hy, map_sub, (hfh _).2 ⟨a, rfl⟩, zero_sub, neg_neg]
end GroundTheory.ProfCoh
