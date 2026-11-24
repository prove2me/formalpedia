-- Prove2me | solution 1 for GlobalTheory.isDominant_fromSpecStalk_genericPoint
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:31:17.699785+00:00
-- url     : https://prove2.me/submissions/bbbb6cf4-0a35-4d6b-8ba0-35f7a56e5809

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_BijectiveAlgebraMapIntegralClosureOfBirational
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueLiftSpecOfIsLocalizationAway

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open GlobalTheory
variable {U T Z Y : Scheme.{u}}
namespace GlobalTheory
theorem _root_.solution (U : Scheme.{u}) [IsIntegral U] :
    IsDominant (U.fromSpecStalk (genericPoint U)) := by
  refine ⟨?_⟩
  have h1 : genericPoint U ∈ Set.range (U.fromSpecStalk (genericPoint U)) := by
    rw [Scheme.range_fromSpecStalk]; exact specializes_rfl
  refine Dense.mono (Set.singleton_subset_iff.mpr h1) ?_
  rw [dense_iff_closure_eq]
  exact genericPoint_spec U
end GlobalTheory
