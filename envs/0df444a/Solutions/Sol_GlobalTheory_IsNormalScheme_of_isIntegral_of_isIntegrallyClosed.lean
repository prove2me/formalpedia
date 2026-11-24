-- Prove2me | solution 1 for GlobalTheory.IsNormalScheme.of_isIntegral_of_isIntegrallyClosed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:35:08.522235+00:00
-- url     : https://prove2.me/submissions/ceb0a7c7-7c20-48da-9495-e1dd5528e027

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsCompletedStrictHens
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIrreducibleGeneralizations
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Theorems.Thm_GlobalTheory_IsNormalScheme_of_forall_exists_opens

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
theorem _root_.solution (X : Scheme.{u}) [IsIntegral X]
    (h : ∀ (U : X.Opens) [Nonempty U], IsAffineOpen U → IsIntegrallyClosed Γ(X, U)) :
    IsNormalScheme X := by
  refine of_forall_exists_opens fun x ↦ ?_
  obtain ⟨_, ⟨U, hU, rfl⟩, hx, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have : Nonempty U := ⟨⟨x, hx⟩⟩
  have := h U hU
  exact ⟨U, hx, (iff_spec_of_isAffineOpen hU).mpr inferInstance⟩
end GlobalTheory.IsNormalScheme
