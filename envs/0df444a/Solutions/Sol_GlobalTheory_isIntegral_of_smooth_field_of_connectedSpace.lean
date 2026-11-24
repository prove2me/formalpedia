-- Prove2me | solution 1 for GlobalTheory.isIntegral_of_smooth_field_of_connectedSpace
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:47:14.268093+00:00
-- url     : https://prove2.me/submissions/7ee93de0-41f8-4f90-a9b2-eb7cb634daa8

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegExp
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsIntegralOfSmoothFieldOfConnectedSpace
import Theorems.Thm_GlobalTheory_IsNormalScheme_isIntegral_of_connectedSpace
import Theorems.Thm_GlobalTheory_forall_isDomain_and_isIntegrallyClosed_stalk_of_smooth


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
theorem _root_.solution {K : Type u} [Field K] {Z : Scheme.{u}}
    (g : Z ⟶ Spec (.of K)) [Smooth g] [ConnectedSpace Z] : IsIntegral Z := by
  have hK : IsNormalScheme (Spec (.of K)) := inferInstance
  have : IsNormalScheme Z := (isNormalScheme_iff Z).mpr
    (forall_isDomain_and_isIntegrallyClosed_stalk_of_smooth g ((isNormalScheme_iff _).mp hK))
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian g
  exact IsNormalScheme.isIntegral_of_connectedSpace Z
end GlobalTheory
