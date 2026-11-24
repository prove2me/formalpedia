-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HCdecomp.HH_NV
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:33:24.548912+00:00
-- url     : https://prove2.me/submissions/2286fae6-477b-407a-9082-06263751b145

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_LowKMultOneP
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_InNOfMem
import Theorems.Thm_GlobalTheory_CompanionTheory_HCdecomp_mem_NV
import Theorems.Thm_GlobalTheory_CompanionTheory_HCdecomp_HH_comm
import Theorems.Thm_CompanionTheory_D_DSIC_lift_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] CompanionTheory.D.DSIC.lift_apply



set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HCdecomp
open Formalism.REAL (GlRel)
open CompanionTheory.D.LK
variable {n : ℕ}
variable {V : Type} [AddCommGroup V] [Module ℂ V]
namespace GlobalTheory.CompanionTheory.HCdecomp
theorem _root_.solution {E : Fin n → Fin n → Module.End ℂ V} (hE : GlRel E) {y : V} (hy : y ∈ NV E) :
    HH E y ∈ NV E := by
  refine Submodule.iSup_induction _ (motive := fun y => HH E y ∈ NV E) hy ?_ ?_ ?_
  · rintro i _ ⟨w, rfl⟩
    have h := LinearMap.congr_fun (HH_comm hE i.1.1 i.1.2) w
    simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply] at h
    rw [sub_eq_iff_eq_add.mp h]
    exact (NV E).add_mem ((NV E).smul_mem _ (mem_NV E i.2 _)) (mem_NV E i.2 _)
  · simp
  · intro x y hx hy
    rw [map_add]; exact (NV E).add_mem hx hy
end GlobalTheory.CompanionTheory.HCdecomp
