-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.CasselmanOsborne.lift_qdet
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:55:20.335432+00:00
-- url     : https://prove2.me/submissions/c39b9071-99b5-4f8a-802c-de74cec8738e

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_ZetaDegZero
import Theorems.Thm_GlobalTheory_CompanionTheory_CasselmanOsborne_pres_qminor
import Theorems.Thm_GlobalTheory_CompanionTheory_CasselmanOsborne_pres_graph
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.CasselmanOsborne
open Formalism.REAL (GlRel qdet qminor Tm)
open CompanionTheory.D.DSIC
variable {n : ℕ} {ε : Fin n → Bool} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
namespace GlobalTheory.CompanionTheory.CasselmanOsborne
theorem _root_.solution (φ : V →ₗ[ℂ] W) (E : Fin n → Fin n → Module.End ℂ V) (F : Fin n → Fin n → Module.End ℂ W)
    (h : ∀ a b x, φ (E a b x) = F a b (φ x)) (u : ℂ) (x : Ch ε V) :
    lift ε φ (lift ε (qdet E u) x) = lift ε (qdet F u) (lift ε φ x) := by
  funext A
  simp only [lift_apply]
  exact (pres_graph φ _ _).1 (pres_qminor E F id id (fun i j => (pres_graph φ _ _).2 (h i j)) u) _
end GlobalTheory.CompanionTheory.CasselmanOsborne
