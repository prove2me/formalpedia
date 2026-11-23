-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HCdecomp.adH_evd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:28:34.581812+00:00
-- url     : https://prove2.me/submissions/6780aabd-f6f5-4fd9-a1a5-b544a9fb9a67

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_LowKMultOneP
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_InNOfMem
import Theorems.Thm_GlobalTheory_CompanionTheory_HCdecomp_HH_comm
import Theorems.Thm_GlobalTheory_CompanionTheory_HCdecomp_adH_apply
import Theorems.Thm_GlobalTheory_CompanionTheory_HCdecomp_adH_mul
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
theorem _root_.solution {E : Fin n → Fin n → Module.End ℂ V} (hE : GlRel E) (b : FreeAlgebra ℂ (Fin n)) :
    adH E (evd (fun c => E c c) b) = 0 := by
  induction b using FreeAlgebra.induction with
  | grade0 r =>
    rw [AlgHom.commutes, adH_apply, Algebra.commutes, sub_self]
  | grade1 c =>
    simp only [evd, FreeAlgebra.lift_ι_apply, adH_apply, HH_comm hE, sub_self, zero_smul]
  | mul a b ha hb => rw [map_mul, adH_mul, ha, hb]; simp
  | add a b ha hb => rw [map_add, map_add, ha, hb, add_zero]
end GlobalTheory.CompanionTheory.HCdecomp
