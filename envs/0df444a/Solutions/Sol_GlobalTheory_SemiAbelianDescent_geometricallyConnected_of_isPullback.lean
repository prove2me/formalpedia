-- Prove2me | solution 1 for GlobalTheory.SemiAbelianDescent.geometricallyConnected_of_isPullback
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:13:37.118083+00:00
-- url     : https://prove2.me/submissions/283dad79-0f94-402b-acfb-caa6a3848614

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AbProj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_OneArc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_GeometricallyConnectedOfIsPullback
import Theorems.Thm_GlobalTheory_SemiAbelianDescent_exists_lift

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory GlobalTheory.SemiAbelianDescent
namespace GlobalTheory.SemiAbelianDescent
theorem _root_.solution {X X' Y Y' : Scheme.{0}} {π : X ⟶ X'} [IsIntegralHom π]
    [Surjective π] {f : Y ⟶ X} {f' : Y' ⟶ X'} {φ : Y ⟶ Y'} (h : IsPullback φ f f' π)
    [GeometricallyConnected f] : GeometricallyConnected f' := by
  refine ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun K _ y => ?_⟩
  let ιK : Spec (CommRingCat.of (AlgebraicClosure K)) ⟶ Spec (CommRingCat.of K) :=
    Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K)))
  obtain ⟨q, hq⟩ := exists_lift π (ιK ≫ y)
  have hA : ConnectedSpace ↥(pullback f q) :=
    GeometricallyConnected.geometrically_connectedSpace _ _ _ (.of_hasPullback _ _)
  have hιK : Surjective ιK := ⟨fun x => ⟨Nonempty.some inferInstance, Subsingleton.elim _ _⟩⟩
  let M := (IsPullback.paste_horiz (IsPullback.of_hasPullback f q) h).isoPullback.hom ≫
    (pullback.congrHom rfl hq).hom ≫ (pullbackLeftPullbackSndIso f' y ιK).inv ≫
      pullback.fst (pullback.snd f' y) ιK
  have hM : Surjective M := by dsimp only [M]; infer_instance
  exact M.surjective.connectedSpace M.continuous
end GlobalTheory.SemiAbelianDescent
