-- Prove2me | solution 1 for GlobalTheory.IsNormalScheme.iff_isIntegrallyClosed_sections
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:00:05.805725+00:00
-- url     : https://prove2.me/submissions/f67c9d7c-531a-4b4c-ab62-2e7b2e4093d9

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsCompletedStrictHens
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIrreducibleGeneralizations
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Theorems.Thm_GlobalTheory_IsNormalScheme_of_isIntegral_of_isIntegrallyClosed

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open GlobalTheory
attribute [instance] IsNormalScheme.isDomain_stalk IsNormalScheme.isIntegrallyClosed_stalk
open GlobalTheory.IsNormalScheme
namespace GlobalTheory.IsNormalScheme
theorem _root_.solution (X : Scheme.{u}) [IsIntegral X] :
    IsNormalScheme X ↔ ∀ (U : X.Opens) [Nonempty U], IsIntegrallyClosed Γ(X, U) :=
  ⟨fun _ _ _ ↦ inferInstance, fun h ↦ of_isIntegral_of_isIntegrallyClosed X fun U _ _ ↦ h U⟩
end GlobalTheory.IsNormalScheme
