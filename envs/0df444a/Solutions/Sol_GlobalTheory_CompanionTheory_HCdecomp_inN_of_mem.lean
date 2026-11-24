-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HCdecomp.inN_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:36:58.886152+00:00
-- url     : https://prove2.me/submissions/d99fe9e1-7fb7-44dc-9329-d8474c326cf1

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_LowKMultOneP
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_InNOfMem
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
theorem _root_.solution (E : Fin n → Fin n → Module.End ℂ V) {y : V} (hy : y ∈ NV E) :
    InN (allT n) E y := by
  classical
  refine Submodule.iSup_induction _ (motive := fun y => InN (allT n) E y) hy ?_ ?_ ?_
  · rintro i _ ⟨w, rfl⟩
    refine ⟨Pi.single i w, ?_⟩
    rw [Finset.sum_eq_single i]
    · simp [cpt]
    · intro j _ hj
      simp [Pi.single_eq_of_ne hj]
    · simp
  · exact ⟨0, by simp⟩
  · rintro x y ⟨w, rfl⟩ ⟨w', rfl⟩
    refine ⟨w + w', ?_⟩
    simp [cpt, Finset.sum_add_distrib]
end GlobalTheory.CompanionTheory.HCdecomp
