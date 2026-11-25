-- Prove2me | solution 1 for GlobalTheory.isIntegral_specialFibre_of_smooth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:40:00.966114+00:00
-- url     : https://prove2.me/submissions/2b878c4a-4e8a-4066-a33d-b098c728bf93

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsCompletedStrictHens
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_AbelianSchemeQuotients_IsAbelianScheme
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_CubicalStructures_CubeSymmetricSwapFirst
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_GeometricallyIntegralIffGeometricallyConnectedOf
import Theorems.Thm_GlobalTheory_isIntegral_pullback_of_smooth

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
variable {X : Scheme.{u}} {V : Type u} [CommRing V]
namespace GlobalTheory
theorem _root_.solution [IsLocalRing V] (f : X ⟶ Spec (.of V)) [Smooth f]
    [GeometricallyConnected f] :
    IsIntegral (pullback f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue V)))) :=
  isIntegral_pullback_of_smooth _ _
end GlobalTheory
