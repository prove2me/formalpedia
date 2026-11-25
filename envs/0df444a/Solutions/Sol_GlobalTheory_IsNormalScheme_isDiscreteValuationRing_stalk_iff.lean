-- Prove2me | solution 1 for GlobalTheory.IsNormalScheme.isDiscreteValuationRing_stalk_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:00:10.770412+00:00
-- url     : https://prove2.me/submissions/6b7d7fb7-1ec5-4cc2-8fb2-7a5681dc3bf4

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
    [IsLocallyNoetherian X] {x : X} :
    IsDiscreteValuationRing (X.presheaf.stalk x) ↔ Order.coheight x = 1 := by
  refine ⟨fun h ↦ ?_, isDiscreteValuationRing_stalk⟩
  have := IsDiscreteValuationRing.ringKrullDim_eq_one (X.presheaf.stalk x)
  rw [ringKrullDim_stalk_eq_coheight] at this
  exact_mod_cast this
end GlobalTheory.IsNormalScheme
