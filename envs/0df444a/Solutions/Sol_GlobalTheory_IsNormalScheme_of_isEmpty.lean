-- Prove2me | solution 1 for GlobalTheory.IsNormalScheme.of_isEmpty
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:55:57.268845+00:00
-- url     : https://prove2.me/submissions/c0e6880a-3c5d-4d37-9ba7-eeb7110bc977

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
theorem _root_.solution (X : Scheme.{u}) [IsEmpty X] : IsNormalScheme X :=
  ⟨isEmptyElim, isEmptyElim⟩
end GlobalTheory.IsNormalScheme
