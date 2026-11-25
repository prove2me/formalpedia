-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HCdecomp.hcdec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T02:24:58.951059+00:00
-- url     : https://prove2.me/submissions/df399e42-4e0e-4e45-891e-ce0138430edd

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_LowKMultOneP
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_InNOfMem
import Theorems.Thm_GlobalTheory_CompanionTheory_HCdecomp_inN_of_mem
import Theorems.Thm_GlobalTheory_CompanionTheory_HCdecomp_adH_apply
import Theorems.Thm_GlobalTheory_CompanionTheory_HCdecomp_adH_evd
import Theorems.Thm_GlobalTheory_CompanionTheory_HCdecomp_mem_JJ_of
import Theorems.Thm_P2M_GlobalTheory_CompanionTheory_HCdecomp_Low_mul__96eb5954ceac
import Theorems.Thm_GlobalTheory_CompanionTheory_HCdecomp_red_all
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
namespace GlobalTheory.CompanionTheory.HCdecomp
theorem _root_.solution : CompanionTheory.D.LK.HCdec := by
  intro n a ha
  obtain ⟨u, hu, h⟩ := red_all a
  obtain ⟨b, hb⟩ := hu.mul'
  refine ⟨b, fun V _ _ E hE x => inN_of_mem E ?_⟩
  have h0 : adH E (ev E a - evd (fun c => E c c) b) = 0 := by
    rw [map_sub, adH_evd hE, sub_zero, adH_apply, sub_eq_zero]
    exact (Commute.sum_left _ _ _ fun c _ => (ha V E hE c).smul_left _).eq
  have := mem_JJ_of hE h0 (hb V E hE) (by simpa using h V E hE)
  exact this x
end GlobalTheory.CompanionTheory.HCdecomp
