-- Prove2me | solution 1 for GlobalTheory.IsNormalScheme.of_forall_exists_opens
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:16:26.215163+00:00
-- url     : https://prove2.me/submissions/3890d547-67fe-44a2-9ff8-ecb4b5c3c2d8

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
theorem _root_.solution {X : Scheme.{u}}
    (h : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧ IsNormalScheme U) : IsNormalScheme X :=
  of_forall_exists_isOpenImmersion fun x ↦ by
    obtain ⟨U, hx, hU⟩ := h x
    exact ⟨U, U.ι, inferInstance, hU, by simpa using hx⟩
end GlobalTheory.IsNormalScheme
