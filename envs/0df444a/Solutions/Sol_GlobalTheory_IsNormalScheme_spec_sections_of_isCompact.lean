-- Prove2me | solution 1 for GlobalTheory.IsNormalScheme.spec_sections_of_isCompact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:55:59.254943+00:00
-- url     : https://prove2.me/submissions/c372de88-1dbb-4713-9b5c-773dbf51452b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsCompletedStrictHens
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIrreducibleGeneralizations
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite

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
theorem _root_.solution {X : Scheme.{u}} [IsNormalScheme X] [IsLocallyNoetherian X]
    {U : X.Opens} (hU : IsCompact (U : Set X)) : IsNormalScheme (Spec Γ(X, U)) :=
  spec_of_isIntegrallyClosedIn hU Γ(X, U)
end GlobalTheory.IsNormalScheme
