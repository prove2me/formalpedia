-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.DSICFRel.lift_rel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:26:19.546943+00:00
-- url     : https://prove2.me/submissions/cd1675da-adf8-4843-b3fb-2061e83c7f3e

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
theorem _root_.solution (E : Fin n → Fin n → Module.End ℂ V) (hE : KRel ε E) :
    KRel ε (fun c d => (lift ε (E c d) : Module.End ℂ (Ch ε V))) := by
  intro a b c d hab hcd
  refine LinearMap.ext fun x => funext fun A => ?_
  have := LinearMap.congr_fun (hE a b c d hab hcd) (x A)
  split_ifs at this ⊢ <;> simpa using this
end GlobalTheory.CompanionTheory.DSICFRel
