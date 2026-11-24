-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.CasselmanOsborne.pres_ofFn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:22:44.681786+00:00
-- url     : https://prove2.me/submissions/09e29a57-a56a-46ae-b6ab-1f60c635c2b6

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_ZetaDegZero
import Theorems.Thm_GlobalTheory_CompanionTheory_CasselmanOsborne_pres_mul
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
variable {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
namespace GlobalTheory.CompanionTheory.CasselmanOsborne
theorem _root_.solution {R : Submodule ℂ (V × W)} : ∀ {t : ℕ} (S : Fin t → Module.End ℂ V)
    (T : Fin t → Module.End ℂ W), (∀ k, Pres R (S k) (T k)) →
    Pres R (List.ofFn S).prod (List.ofFn T).prod
  | 0, _, _, _ => by
    intro x y hxy
    simpa using hxy
  | t + 1, S, T, h => by
    rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons]
    exact pres_mul (h 0) (solution _ _ fun k => h k.succ)
end GlobalTheory.CompanionTheory.CasselmanOsborne
