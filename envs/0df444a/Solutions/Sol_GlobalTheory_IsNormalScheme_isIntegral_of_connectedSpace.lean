-- Prove2me | solution 1 for GlobalTheory.IsNormalScheme.isIntegral_of_connectedSpace
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:46:26.613589+00:00
-- url     : https://prove2.me/submissions/78619baa-48a7-40ca-a579-a36a6dbf546e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsCompletedStrictHens
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIrreducibleGeneralizations
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Theorems.Thm_GlobalTheory_IsNormalScheme_connectedComponent_eq_irreducibleComponent

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
theorem _root_.solution (X : Scheme.{u}) [IsNormalScheme X] [IsLocallyNoetherian X]
    [ConnectedSpace X] : IsIntegral X := by
  obtain ⟨x⟩ : Nonempty X := inferInstance
  have : IrreducibleSpace X := by
    rw [irreducibleSpace_def, Set.top_eq_univ, ← PreconnectedSpace.connectedComponent_eq_univ x,
      connectedComponent_eq_irreducibleComponent]
    exact isIrreducible_irreducibleComponent
  exact isIntegral_of_irreducibleSpace X
end GlobalTheory.IsNormalScheme
