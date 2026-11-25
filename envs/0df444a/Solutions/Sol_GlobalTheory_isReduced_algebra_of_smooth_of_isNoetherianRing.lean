-- Prove2me | solution 1 for GlobalTheory.isReduced_algebra_of_smooth_of_isNoetherianRing
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:47:23.973856+00:00
-- url     : https://prove2.me/submissions/5b013d88-7b95-4c53-98fb-7165d7aa123b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_AbelianSchemeQuotients_IsAbelianScheme
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_DimSplitPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_GeometricallyIntegralIffGeometricallyConnectedOf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HomBaseChangeBijectiveOfLeNilradical
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentationDiagMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_BijectiveRestrictPointsOfEtaleOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsReducedAlgebraOfSmoothOfIsNoetherianRing
import Theorems.Thm_GlobalTheory_geometricallyReduced_of_smooth


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory
theorem _root_.solution (A B : Type) [CommRing A] [CommRing B]
    [Algebra A B] [Algebra.Smooth A B] [IsNoetherianRing A] [_root_.IsReduced A] :
    _root_.IsReduced B := by

  let f : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of A) :=
    Spec.map (CommRingCat.ofHom (algebraMap A B))
  have : Smooth f := HasRingHomProperty.Spec_iff.mpr (RingHom.smooth_algebraMap.mpr inferInstance)
  have : GeometricallyReduced f := GlobalTheory.geometricallyReduced_of_smooth f
  have : _root_.IsReduced (CommRingCat.of A) := inferInstanceAs (_root_.IsReduced A)
  have : IsNoetherianRing (CommRingCat.of A) := inferInstanceAs (IsNoetherianRing A)
  have : IsReduced (Spec (CommRingCat.of B)) :=
    GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian f
  exact (affine_isReduced_iff (CommRingCat.of B)).mp inferInstance
end GlobalTheory
