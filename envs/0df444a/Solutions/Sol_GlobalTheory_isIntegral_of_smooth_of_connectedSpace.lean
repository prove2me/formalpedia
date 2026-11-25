-- Prove2me | solution 1 for GlobalTheory.isIntegral_of_smooth_of_connectedSpace
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:53:32.548328+00:00
-- url     : https://prove2.me/submissions/94e968b8-6ba7-4926-baab-7d8eea12a0b6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsCompletedStrictHens
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_AbelianSchemeQuotients_IsAbelianScheme
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_CubicalStructures_CubeSymmetricSwapFirst
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_GeometricallyIntegralIffGeometricallyConnectedOf
import Theorems.Thm_GlobalTheory_isNormalScheme_of_smooth
import Theorems.Thm_GlobalTheory_IsNormalScheme_isIntegral_of_connectedSpace


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
theorem _root_.solution (f : X ⟶ S) [Smooth f] [IsNormalScheme S]
    [IsLocallyNoetherian S] [ConnectedSpace X] : IsIntegral X :=
  have := isNormalScheme_of_smooth f
  have := LocallyOfFiniteType.isLocallyNoetherian f
  IsNormalScheme.isIntegral_of_connectedSpace X
end GlobalTheory
