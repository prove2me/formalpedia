-- Prove2me | solution 1 for GlobalTheory.GlobalFunctions.eq_zero_of_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:53:47.856558+00:00
-- url     : https://prove2.me/submissions/928ffb11-d225-451d-a795-f9ed222a643d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsFiniteProjectiveComplexQuasiIso
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoAppTopOfIsPullbackOfSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsAppTopEqOfEffectiveEpi
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsIsoAppTopOfIsAffine
import Theorems.Thm_GlobalTheory_GlobalFunctions_exists_eq_of_eq
import Theorems.Thm_GlobalTheory_GlobalFunctions_appTop_comp_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
open TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open GlobalTheory.GlobalFunctions
variable {R B C : CommRingCat.{0}} {X : Scheme.{0}}
namespace GlobalTheory.GlobalFunctions
theorem _root_.solution {p : X ⟶ Spec R} (hp : Function.Surjective p.appTop)
    (i : Spec B ⟶ X) [EffectiveEpi i] {f g : B ⟶ C}
    (H : IsPullback (Spec.map f) (Spec.map g) i i) {φ : R ⟶ B} (hφ : i ≫ p = Spec.map φ)
    {R' : CommRingCat.{0}} (r : B ⟶ R') (hr : Function.Injective (φ ≫ r)) (x : B)
    (hx : f x = g x) (hrx : r x = 0) : x = 0 := by
  obtain ⟨a, rfl⟩ := exists_eq_of_eq i H x hx
  obtain ⟨c, rfl⟩ := hp a
  rw [← CommRingCat.comp_apply p.appTop, appTop_comp_eq hφ, CommRingCat.comp_apply] at hrx ⊢
  have : (Scheme.ΓSpecIso R).hom c = 0 := hr (hrx.trans (map_zero _).symm)
  rw [this, map_zero]
end GlobalTheory.GlobalFunctions
