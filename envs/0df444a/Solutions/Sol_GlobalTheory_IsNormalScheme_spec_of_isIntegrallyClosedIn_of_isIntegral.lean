-- Prove2me | solution 1 for GlobalTheory.IsNormalScheme.spec_of_isIntegrallyClosedIn_of_isIntegral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:16:08.297661+00:00
-- url     : https://prove2.me/submissions/0d94b216-f42d-4aa7-bc5c-e5a21944b83d

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
    [IsIntegral X] (U : X.Opens) (A : Type u) [CommRing A] [Algebra A Γ(X, U)]
    [IsIntegrallyClosedIn A Γ(X, U)] : IsNormalScheme (Spec (.of A)) := by
  have hinj : Function.Injective (algebraMap A Γ(X, U)) :=
    IsIntegralClosure.algebraMap_injective A A _
  by_cases h : Nonempty U
  · have : IsDomain A := hinj.isDomain _
    have : FaithfulSMul A Γ(X, U) := (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
    have : IsIntegrallyClosed A := .of_isIntegrallyClosed_of_isIntegrallyClosedIn _ Γ(X, U)
    infer_instance
  · have hU : U = ⊥ := by
      by_contra hU
      exact h ((Opens.ne_bot_iff_nonempty _).mp hU).to_subtype
    have : Subsingleton Γ(X, U) :=
      CommRingCat.subsingleton_of_isTerminal (X.sheaf.isTerminalOfEqEmpty hU)
    have : Subsingleton A := hinj.subsingleton
    refine (spec_iff _).mpr fun p hp ↦ (hp.ne_top (Subsingleton.elim _ _)).elim
end GlobalTheory.IsNormalScheme
