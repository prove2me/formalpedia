-- Prove2me | solution 1 for GlobalTheory.IsNormalScheme.iff_forall_isAffineOpen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:47:45.878643+00:00
-- url     : https://prove2.me/submissions/b2b5fb7b-f456-402a-bc6b-da89f77e5497

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsCompletedStrictHens
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIrreducibleGeneralizations
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Theorems.Thm_GlobalTheory_IsNormalScheme_iff_of_iSup_eq_top

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
theorem _root_.solution (X : Scheme.{u}) :
    IsNormalScheme X ↔ ∀ U : X.Opens, IsAffineOpen U → ∀ (p : Ideal Γ(X, U)) [p.IsPrime],
      IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p) := by
  refine ⟨fun _ U hU ↦ (spec_iff _).mp (spec_of_isAffineOpen hU), fun h ↦ ?_⟩
  rw [iff_of_iSup_eq_top _ (iSup_affineOpens_eq_top X)]
  exact fun U ↦ (iff_spec_of_isAffineOpen U.2).mpr ((spec_iff _).mpr (h U U.2))
end GlobalTheory.IsNormalScheme
