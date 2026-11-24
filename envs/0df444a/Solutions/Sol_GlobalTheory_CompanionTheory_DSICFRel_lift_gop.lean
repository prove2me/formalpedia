-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.DSICFRel.lift_gop
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:26:18.6039+00:00
-- url     : https://prove2.me/submissions/fe06f572-339b-42ca-82d2-be497e46a3d1

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_CarImpFrel
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
open Finset CompanionTheory.D.DSIC
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.DSICFRel
variable {n : ℕ}
variable {ε : Fin n → Bool} {V : Type} [AddCommGroup V] [Module ℂ V]
namespace GlobalTheory.CompanionTheory.DSICFRel
theorem _root_.solution (T : Module.End ℂ V) (c d : Fin n) :
    Commute (lift ε T : Module.End ℂ (Ch ε V)) (Gop ε c d) := by
  have ha : ∀ i : NC ε, Commute (lift ε T : Module.End ℂ (Ch ε V)) (ann i) := by
    intro i
    refine LinearMap.ext fun x => funext fun A => ?_
    by_cases h : i ∈ A <;> simp [ann, h]
  have hc : ∀ i : NC ε, Commute (lift ε T : Module.End ℂ (Ch ε V)) (cre i) := by
    intro i
    refine LinearMap.ext fun x => funext fun A => ?_
    by_cases h : i ∈ A <;> simp [cre, h]
  unfold Gop
  exact Commute.sum_right _ _ _ fun i _ => Commute.sum_right _ _ _ fun j _ =>
    ((hc i).mul_right (ha j)).smul_right _
end GlobalTheory.CompanionTheory.DSICFRel
