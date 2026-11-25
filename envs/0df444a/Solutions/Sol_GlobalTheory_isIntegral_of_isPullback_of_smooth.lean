-- Prove2me | solution 1 for GlobalTheory.isIntegral_of_isPullback_of_smooth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:19:45.005364+00:00
-- url     : https://prove2.me/submissions/2ef9a6f2-a64e-45ad-abe5-66560e815955

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsCompletedStrictHens
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_AbelianSchemeQuotients_IsAbelianScheme
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_CubicalStructures_CubeSymmetricSwapFirst
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_GeometricallyIntegralIffGeometricallyConnectedOf
import Theorems.Thm_GlobalTheory_isIntegral_of_smooth_of_geometricallyConnected

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory
open GlobalTheory
variable {X Y S : Scheme.{u}}
namespace GlobalTheory
theorem _root_.solution {Z : Scheme.{u}} {fst : Z ⟶ X} {snd : Z ⟶ Y}
    {f : X ⟶ S} {g : Y ⟶ S} (h : IsPullback fst snd f g) [Smooth f] [GeometricallyConnected f]
    [IsIntegral Y] : IsIntegral Z :=
  have : Smooth snd := MorphismProperty.of_isPullback h ‹_›
  have : GeometricallyConnected snd := MorphismProperty.of_isPullback h ‹_›
  isIntegral_of_smooth_of_geometricallyConnected snd
end GlobalTheory
