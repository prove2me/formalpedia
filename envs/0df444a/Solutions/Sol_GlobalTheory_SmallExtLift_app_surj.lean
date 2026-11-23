-- Prove2me | solution 1 for GlobalTheory.SmallExtLift.app_surj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:42:46.955865+00:00
-- url     : https://prove2.me/submissions/1ca351c4-8e15-452d-a1ae-7052ae625d11

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_ConstPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsGenOfSmallExtension

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
open TopologicalSpace
attribute [local instance] Over.cartesianMonoidalCategory
set_option backward.isDefEq.respectTransparency false
noncomputable section
open GlobalTheory GlobalTheory.SmallExtLift
variable {X Y Z : Scheme.{0}}
variable {R : Type} [CommRing R]
variable {R' : Type} [CommRing R'] {φ : R →+* R'} {p : X ⟶ Spec (CommRingCat.of R)}
  {π : Y ⟶ X} {f' : Y ⟶ Spec (CommRingCat.of R')}
namespace GlobalTheory.SmallExtLift
theorem _root_.solution (hφ : Function.Surjective φ)
    (H : IsPullback π f' p (Spec.map (CommRingCat.ofHom φ))) {V : X.Opens} (hV : IsAffineOpen V) :
    Function.Surjective (π.app V).hom := by
  have : IsClosedImmersion (Spec.map (CommRingCat.ofHom φ)) :=
    IsClosedImmersion.spec_of_surjective _ hφ
  have : IsClosedImmersion π := MorphismProperty.of_isPullback H.flip this
  exact π.app_surjective V hV
end GlobalTheory.SmallExtLift
