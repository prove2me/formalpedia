-- Prove2me | solution 1 for GlobalTheory.geometricallyIntegral_of_smooth_of_geometricallyConnected_fibres
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:53:35.311147+00:00
-- url     : https://prove2.me/submissions/6b02209b-29a5-40d6-88e1-0993e97c8eab

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegExp
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsIntegralOfSmoothFieldOfConnectedSpace
import Theorems.Thm_GlobalTheory_isIntegral_of_smooth_field_of_connectedSpace

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
universe u
namespace GlobalTheory
theorem _root_.solution {X S : Scheme.{u}}
    (f : X ⟶ S) [Smooth f] [GeometricallyConnected f] : GeometricallyIntegral f := by
  refine ⟨fun K _ y Z fst snd h ↦ ?_⟩
  have : Smooth snd := MorphismProperty.of_isPullback (P := @Smooth) h ‹_›
  have : ConnectedSpace Z := GeometricallyConnected.geometrically_connectedSpace y fst snd h
  exact isIntegral_of_smooth_field_of_connectedSpace snd
end GlobalTheory
