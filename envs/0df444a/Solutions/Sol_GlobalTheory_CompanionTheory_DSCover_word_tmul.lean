-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.DSCover.word_tmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:25:46.47291+00:00
-- url     : https://prove2.me/submissions/9b8882a3-6f04-4fc9-8907-619d54911163

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_WordMonomial
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
open scoped TensorProduct
open MvPolynomial
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.DSCover
open Formalism.REAL (GlRel)
open CompanionTheory.D.DSIC
variable {σ : Type}
variable {V : Type} [AddCommGroup V] [Module ℂ V]
namespace GlobalTheory.CompanionTheory.DSCover
theorem _root_.solution (l : List σ) (v : V) (f : MvPolynomial σ ℂ) :
    (l.map fun i => ((pd i).lTensor V : Module.End ℂ (V ⊗[ℂ] MvPolynomial σ ℂ))).prod (v ⊗ₜ f) =
      v ⊗ₜ (l.map pd).prod f := by
  induction l with
  | nil => simp
  | cons i l ih => simp only [List.map_cons, List.prod_cons, Module.End.mul_apply, ih, LinearMap.lTensor_tmul]
end GlobalTheory.CompanionTheory.DSCover
