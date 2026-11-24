-- Prove2me | solution 1 for GlobalTheory.IsNormalScheme.connectedComponent_eq_irreducibleComponent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:31:08.226795+00:00
-- url     : https://prove2.me/submissions/be644931-8644-4864-921b-afc67338213e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsCompletedStrictHens
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIrreducibleGeneralizations
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Theorems.Thm_GlobalTheory_IsNormalScheme_isClopen_of_mem_irreducibleComponents

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
theorem _root_.solution {X : Scheme.{u}} [IsNormalScheme X]
    [IsLocallyNoetherian X] (x : X) : connectedComponent x = irreducibleComponent x :=
  ((isClopen_of_mem_irreducibleComponents
    (irreducibleComponent_mem_irreducibleComponents x)).connectedComponent_subset
      mem_irreducibleComponent).antisymm irreducibleComponent_subset_connectedComponent
end GlobalTheory.IsNormalScheme
