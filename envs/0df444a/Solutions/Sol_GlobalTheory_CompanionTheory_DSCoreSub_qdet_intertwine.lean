-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.DSCoreSub.qdet_intertwine
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:43:47.721303+00:00
-- url     : https://prove2.me/submissions/77913c13-1292-4370-9a4b-10e91aa211d2

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_AlgCoreSubOfAlgCore
import Theorems.Thm_GlobalTheory_CompanionTheory_DSCoreSub_ofFn_prod_intertwine
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
theorem _root_.solution (φ : V' →ₗ[ℂ] V) (E' : Fin n → Fin n → Module.End ℂ V')
    (E : Fin n → Fin n → Module.End ℂ V) (h : ∀ a b x, φ (E' a b x) = E a b (φ x)) (u : ℂ) (x : V') :
    φ (qdet E' u x) = qdet E u (φ x) := by
  unfold qdet qminor
  simp only [LinearMap.sum_apply, map_sum, Module.End.mul_apply, Module.End.intCast_apply, map_zsmul]
  refine Finset.sum_congr rfl fun σ _ => ?_
  congr 1
  refine ofFn_prod_intertwine φ _ _ (fun k y => ?_) x
  unfold Tm
  split_ifs <;> simp [h, Module.algebraMap_end_apply]
end GlobalTheory.CompanionTheory.DSCoreSub
