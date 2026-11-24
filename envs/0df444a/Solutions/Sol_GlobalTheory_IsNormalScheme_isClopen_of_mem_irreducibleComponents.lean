-- Prove2me | solution 1 for GlobalTheory.IsNormalScheme.isClopen_of_mem_irreducibleComponents
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:15:40.66883+00:00
-- url     : https://prove2.me/submissions/63a07b87-4c10-4511-8682-8c414368107f

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
theorem _root_.solution {X : Scheme.{u}} [IsNormalScheme X]
    [IsLocallyNoetherian X] {Z : Set X} (hZ : Z ∈ irreducibleComponents X) : IsClopen Z :=
  ⟨isClosed_of_mem_irreducibleComponents Z hZ, isOpen_of_mem_irreducibleComponents hZ⟩
end GlobalTheory.IsNormalScheme
