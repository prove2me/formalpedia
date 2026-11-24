-- Prove2me | solution 1 for GlobalTheory.T.exists_nhds_zero_translation_invariant_of_locallyConstant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:18:04.284263+00:00
-- url     : https://prove2.me/submissions/0c63dd54-6e79-41f2-a243-d62eec2f294c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsNhdsZeroTranslationInvariantOfLocallyConst
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsNhdsZeroTranslationInvariantOfLocallyConstStatement
import Theorems.Thm_GlobalTheory_isTest_nhds_inv


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (X : Type) [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X] (f : X → ℂ), IsTest f → ∃ U ∈ 𝓝 (0 : X), ∀ x : X, ∀ u ∈ U, f (x + u) = f x := by
  first | exact @GlobalTheory.isTest_nhds_inv | exact GlobalTheory.isTest_nhds_inv | (intros; apply GlobalTheory.isTest_nhds_inv <;> assumption)
end _root_.GlobalTheory.T
