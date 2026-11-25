-- Prove2me | solution 1 for GlobalTheory.UnitRigidity.geometricallyConnected_of_isPullback_of_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:25:35.911572+00:00
-- url     : https://prove2.me/submissions/54d61b60-47d2-4719-86b2-75e4fc4f44d2

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_GeometricallyIntegralIffGeometricallyConnectedOf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentationDiagMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_UnitOnProductEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_GeometricallyConnectedOfIsPullbackOfSurjective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.UnitRigidity
namespace GlobalTheory.UnitRigidity
theorem _root_.solution {P X Y Z : Scheme.{0}} {a : P ⟶ X}
    {b : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z} (h : IsPullback a b f g) [Surjective g]
    [GeometricallyConnected b] : GeometricallyConnected f := by
  refine ⟨fun k _ y W fst snd hW => ?_⟩
  obtain ⟨z, -⟩ := (pullback.snd g y).surjective (Classical.arbitrary _)
  let p := (pullback g y).fromSpecResidueField z
  have : Surjective (p ≫ pullback.snd g y) := ⟨fun x => ⟨Classical.arbitrary _, Subsingleton.elim _ _⟩⟩
  have h1 := (IsPullback.of_hasPullback snd (p ≫ pullback.snd g y)).paste_horiz hW
  rw [Category.assoc, ← pullback.condition, ← Category.assoc] at h1
  have h2 := IsPullback.of_right (by rwa [h.lift_fst]) (h.lift_snd _ _ h1.w) h
  have : ConnectedSpace ↥(pullback snd (p ≫ pullback.snd g y)) :=
    GeometricallyConnected.geometrically_connectedSpace _ _ _ h2
  exact (pullback.fst snd (p ≫ pullback.snd g y)).surjective.connectedSpace
    (pullback.fst snd (p ≫ pullback.snd g y)).continuous
end GlobalTheory.UnitRigidity
