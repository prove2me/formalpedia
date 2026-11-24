-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.KoszulBd.glRel_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:48:27.548813+00:00
-- url     : https://prove2.me/submissions/d1038e7c-64c0-4daf-b48a-367c2a9a7f59

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_CommuteOfUnitaryConjugate
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
open Finset
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.KoszulBd
open CompanionTheory.D.DSIC
open Formalism.REAL (GlRel)
variable {n : ℕ} {ε : Fin n → Bool}
variable {V : Type} [AddCommGroup V] [Module ℂ V]
namespace GlobalTheory.CompanionTheory.KoszulBd
theorem _root_.solution (E : Fin n → Fin n → Module.End ℂ V) (hE : GlRel E) :
    GlRel (fun a b => (lift ε (E a b) : Module.End ℂ (Ch ε V))) := by
  have hm : ∀ S U : Module.End ℂ V, (lift ε S : Module.End ℂ (Ch ε V)) * lift ε U = lift ε (S * U) :=
    fun S U => LinearMap.ext fun x => funext fun A => rfl
  have hs : ∀ S U : Module.End ℂ V, (lift ε S : Module.End ℂ (Ch ε V)) - lift ε U = lift ε (S - U) :=
    fun S U => LinearMap.ext fun x => funext fun A => rfl
  have h0 : (lift ε (0 : Module.End ℂ V) : Module.End ℂ (Ch ε V)) = 0 :=
    LinearMap.ext fun x => funext fun A => rfl
  intro a b c d
  try dsimp only
  rw [hm, hm, hs, hE a b c d]
  split_ifs <;> simp only [← h0, hs]
end GlobalTheory.CompanionTheory.KoszulBd
