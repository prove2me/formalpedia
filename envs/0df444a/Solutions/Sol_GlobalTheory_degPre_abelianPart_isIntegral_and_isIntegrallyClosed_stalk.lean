-- Prove2me | solution 1 for GlobalTheory.degPre_abelianPart_isIntegral_and_isIntegrallyClosed_stalk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:53:33.88942+00:00
-- url     : https://prove2.me/submissions/565f50a3-c32a-450c-ae2d-3f1df4f5400f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DataRigidTorsionOfDataRigid
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsIntegralOfSmoothFieldOfConnectedSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsReducedIsNormalSchemeIsLocallyNoetherianOfSmoo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_DegPreAbelianPartIsIntegralAndIsIntegrallyClosed
import Theorems.Thm_GlobalTheory_isIntegral_of_smooth_field_of_connectedSpace
import Theorems.Thm_GlobalTheory_isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F]
      [Algebra (FractionRing R) F], IsIntegral (DegPre.BF D F).left ∧
        ∀ y : (DegPre.BF D F).left, IsIntegrallyClosed ((DegPre.BF D F).left.presheaf.stalk y) := by
  intro R _ _ D F _ _
  have h₁ := D.P.isAb.smooth
  have h₂ := D.P.isAb.geomConnected
  let j : Spec (CommRingCat.of F) ⟶ Spec (CommRingCat.of R) := DegPre.jFR (R := R) F
  let g : (DegPre.BF D F).left ⟶ Spec (CommRingCat.of F) := pullback.fst j D.P.A.hom
  have hs : Smooth g := inferInstanceAs (Smooth (pullback.fst j D.P.A.hom))
  have hc : ConnectedSpace (DegPre.BF D F).left :=
    GeometricallyConnected.geometrically_connectedSpace (f := D.P.A.hom) j
      (pullback.snd j D.P.A.hom) (pullback.fst j D.P.A.hom) (IsPullback.of_hasPullback j D.P.A.hom).flip
  exact ⟨isIntegral_of_smooth_field_of_connectedSpace g, fun y ↦
    ((isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field F _ g hs).2.1 y).2⟩
end GlobalTheory
