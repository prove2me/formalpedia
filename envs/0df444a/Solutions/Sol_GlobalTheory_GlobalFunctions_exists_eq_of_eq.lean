-- Prove2me | solution 1 for GlobalTheory.GlobalFunctions.exists_eq_of_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T16:32:53.916277+00:00
-- url     : https://prove2.me/submissions/2f35fa91-9c3b-4297-ada6-5d75472fa431

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsFiniteProjectiveComplexQuasiIso
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoAppTopOfIsPullbackOfSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsAppTopEqOfEffectiveEpi
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsIsoAppTopOfIsAffine
import Theorems.Thm_GlobalTheory_FlatDescent_exists_appTop_eq_of_effectiveEpi


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
theorem _root_.solution (i : Spec B ⟶ X) [EffectiveEpi i] {f g : B ⟶ C}
    (H : IsPullback (Spec.map f) (Spec.map g) i i) (x : B) (hx : f x = g x) :
    ∃ a : Γ(X, ⊤), (i.appTop ≫ (Scheme.ΓSpecIso B).hom) a = x := by
  obtain ⟨a, ha⟩ := FlatDescent.exists_appTop_eq_of_effectiveEpi i H
    ((Scheme.ΓSpecIso B).inv x) (by
      rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality,
        ← Scheme.ΓSpecIso_inv_naturality, CommRingCat.comp_apply, CommRingCat.comp_apply, hx])
  exact ⟨a, by rw [CommRingCat.comp_apply, ha, Iso.inv_hom_id_apply]⟩
end GlobalTheory.GlobalFunctions
