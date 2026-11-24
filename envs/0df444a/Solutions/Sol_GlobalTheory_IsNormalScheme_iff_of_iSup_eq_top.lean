-- Prove2me | solution 1 for GlobalTheory.IsNormalScheme.iff_of_iSup_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:32:47.329454+00:00
-- url     : https://prove2.me/submissions/0bb1971d-7e06-4f59-b027-92c7bb37a9db

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
theorem _root_.solution {X : Scheme.{u}} {ι : Sort*} (U : ι → X.Opens) (hU : iSup U = ⊤) :
    IsNormalScheme X ↔ ∀ i, IsNormalScheme (U i) := by
  refine ⟨fun _ _ ↦ inferInstance, fun h ↦ of_forall_exists_opens fun x ↦ ?_⟩
  have hx : x ∈ iSup U := hU ▸ trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
  exact ⟨U i, hi, h i⟩
end GlobalTheory.IsNormalScheme
