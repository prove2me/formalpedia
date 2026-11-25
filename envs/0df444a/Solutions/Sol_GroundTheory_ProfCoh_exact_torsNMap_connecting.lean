-- Prove2me | solution 1 for GroundTheory.ProfCoh.exact_torsNMap_connecting
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:24:42.634918+00:00
-- url     : https://prove2.me/submissions/15604cc6-378c-4ac3-8287-2142c2b03563

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
theorem _root_.solution : Function.Exact (torsNMap n h) (connecting hh hfh hf) := by
  intro c
  obtain ⟨b, a, hb, ha⟩ := exists_lift hh hfh c
  rw [connecting_spec hh hfh hf c b a hb ha, modN_mk_eq_zero_iff]
  constructor
  · rintro ⟨a₁, ha₁⟩
    have hb₁ : n • (b - f a₁) = 0 := by rw [smul_sub, ← ha, ← map_nsmul, ha₁, sub_self]
    refine ⟨⟨b - f a₁, (mem_ker_lsmul_iff n _).2 hb₁⟩, Subtype.ext ?_⟩
    simp [hb, (hfh _).2 ⟨a₁, rfl⟩]
  · rintro ⟨t, rfl⟩
    have h₀ := connecting_spec hh hfh hf (torsNMap n h t) t 0 rfl
      (by rw [map_zero, (mem_ker_lsmul_iff n (t : B)).1 t.2])
    rw [connecting_spec hh hfh hf _ b a hb ha, Submodule.Quotient.eq, sub_zero] at h₀
    simpa [eq_comm] using h₀
end GroundTheory.ProfCoh
