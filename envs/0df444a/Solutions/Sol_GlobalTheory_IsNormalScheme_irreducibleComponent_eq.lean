-- Prove2me | solution 1 for GlobalTheory.IsNormalScheme.irreducibleComponent_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:03:26.660354+00:00
-- url     : https://prove2.me/submissions/888d2fbc-b487-4719-849d-2ccdd1a592b6

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
theorem _root_.solution {X : Scheme.{u}} [IsNormalScheme X] {x : X} {Z : Set X}
    (hZ : Z ∈ irreducibleComponents X) (hx : x ∈ Z) : irreducibleComponent x = Z :=
  eq_of_mem_irreducibleComponents (irreducibleComponent_mem_irreducibleComponents x) hZ
    mem_irreducibleComponent hx
end GlobalTheory.IsNormalScheme
