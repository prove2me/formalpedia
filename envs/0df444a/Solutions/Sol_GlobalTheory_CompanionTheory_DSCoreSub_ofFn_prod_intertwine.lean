-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.DSCoreSub.ofFn_prod_intertwine
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:26:27.7618+00:00
-- url     : https://prove2.me/submissions/e81c1bf4-4cee-4312-bfc5-cfd6c2fd11ec

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_AlgCoreSubOfAlgCore
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
open Formalism.REAL CompanionTheory.D.DSIC
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.DSCoreSub
variable {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] {n : ℕ}
namespace GlobalTheory.CompanionTheory.DSCoreSub
theorem _root_.solution (φ : V' →ₗ[ℂ] V) :
    ∀ {t : ℕ} (f' : Fin t → Module.End ℂ V') (f : Fin t → Module.End ℂ V),
      (∀ k x, φ (f' k x) = f k (φ x)) → ∀ x, φ ((List.ofFn f').prod x) = (List.ofFn f).prod (φ x)
  | 0, _, _, _, x => by simp
  | t + 1, f', f, h, x => by
    rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons, Module.End.mul_apply,
      Module.End.mul_apply, h, solution φ _ (fun k => f k.succ) (fun k => h k.succ)]
end GlobalTheory.CompanionTheory.DSCoreSub
