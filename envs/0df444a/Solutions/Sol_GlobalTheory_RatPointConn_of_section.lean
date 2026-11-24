-- Prove2me | solution 1 for GlobalTheory.RatPointConn.of_section
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:11:38.272676+00:00
-- url     : https://prove2.me/submissions/b6769f1a-94d5-4824-8403-4ce934470bc4

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_GeometricallyConnectedOfRatPoint
import Theorems.Thm_GlobalTheory_RatPointConn_fibre_subsingleton
import Theorems.Thm_GlobalTheory_RatPointConn_of_isAlgClosed
import Theorems.Thm_GlobalTheory_RatPointConn_preconnectedSpace_of_fibre
import Theorems.Thm_GlobalTheory_RatPointConn_of_isPullback

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
open GlobalTheory GlobalTheory.RatPointConn
universe u
namespace GlobalTheory.RatPointConn
theorem _root_.solution {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [LocallyOfFiniteType f] [ConnectedSpace X] (s : Spec (.of k) ⟶ X) (hs : s ≫ f = 𝟙 _) :
    GeometricallyConnected f := by
  let y : Spec (.of (AlgebraicClosure k)) ⟶ Spec (.of k) :=
    Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))
  have hy : Surjective y := ⟨fun a => ⟨Classical.arbitrary _, Subsingleton.elim _ _⟩⟩
  have hi : IsIntegralHom y := by
    rw [IsIntegralHom.SpecMap_iff]
    exact algebraMap_isIntegral_iff.2 inferInstance
  have h := IsPullback.of_hasPullback f y
  have ho : UniversallyOpen (pullback.fst f y) := MorphismProperty.of_isPullback h.flip
    (inferInstance : UniversallyOpen y)
  have : PreconnectedSpace ↥(pullback f y) :=
    preconnectedSpace_of_fibre (pullback.fst f y).isOpenMap (pullback.fst f y).isClosedMap _
      (fibre_subsingleton h s hs)
  have : ConnectedSpace ↥(pullback f y) :=
    ⟨((pullback.fst f y).surjective (Classical.arbitrary X)).nonempty⟩
  have := of_isAlgClosed (pullback.snd f y)
  exact of_isPullback h
end GlobalTheory.RatPointConn
