-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HCdecomp.red_all
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T02:04:50.213925+00:00
-- url     : https://prove2.me/submissions/3ff54e38-5cc4-42c8-9d89-064c5af30389

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_LowKMultOneP
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_InNOfMem
import Theorems.Thm_GlobalTheory_CompanionTheory_HCdecomp_Red_add
import Theorems.Thm_GlobalTheory_CompanionTheory_HCdecomp_Red_smul
import Theorems.Thm_GlobalTheory_CompanionTheory_HCdecomp_Red_of_low
import Theorems.Thm_P2M_GlobalTheory_CompanionTheory_HCdecomp_Red_mul___00b8b2883c0d
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
theorem _root_.solution (a : FreeAlgebra ℂ (Fin n × Fin n)) : Red a := by
  have : ∀ z, Red z → Red (z * a) := by
    induction a using FreeAlgebra.induction with
    | grade0 r =>
      intro z hz
      rw [← Algebra.commutes, ← Algebra.smul_def]
      exact hz.smul r
    | grade1 p => exact fun z hz => hz.mul_ι p
    | mul a b ha hb => intro z hz; rw [← mul_assoc]; exact hb _ (ha _ hz)
    | add a b ha hb => intro z hz; rw [mul_add]; exact (ha _ hz).add (hb _ hz)
  simpa using this 1 (Red.of_low Low.one)
end GlobalTheory.CompanionTheory.HCdecomp
