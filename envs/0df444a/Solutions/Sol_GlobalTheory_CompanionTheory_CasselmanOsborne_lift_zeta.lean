-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.CasselmanOsborne.lift_zeta
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:13:50.085526+00:00
-- url     : https://prove2.me/submissions/bde25144-0502-4b1c-bb18-19a86c95cb5d

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_ZetaDegZero
import Theorems.Thm_GlobalTheory_CompanionTheory_CasselmanOsborne_pres_zeta
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
theorem _root_.solution (hG : GFacts) (φ : V →ₗ[ℂ] W) (E : Fin n → Fin n → Module.End ℂ V)
    (F : Fin n → Fin n → Module.End ℂ W)
    (h : ∀ a b x, φ (E a b x) = F a b (φ x)) (u : ℂ) (x : Ch ε V) :
    lift ε φ (zeta ε (Fop ε E) u x) = zeta ε (Fop ε F) u (lift ε φ x) := by
  obtain ⟨g, hg, -⟩ := hG n ε
  refine (pres_graph (lift ε φ) _ _).1 (pres_zeta ε _ _ (fun c d _ => (pres_graph _ _ _).2 fun x => ?_) u) x
  funext A
  simp [Fop, hg, h, map_sum]
end GlobalTheory.CompanionTheory.CasselmanOsborne
