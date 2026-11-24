-- Prove2me | solution 1 for GlobalTheory.T.isLocallyConstantCompactSupport_mixedModelPartialFourierColumn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:16:10.327693+00:00
-- url     : https://prove2.me/submissions/763067de-860c-4829-a2d0-07ac34a2e503

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocallyConstantCompactSupportMixedModelPartial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_RowMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedStandardAddCharConductorPropertiesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocallyConstantCompactSupportMixedModelPartialStatement
import Theorems.Thm_GlobalTheory_JR_WeilMix_ptrB_isTest


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
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (M : Meas r F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ f : Gl r F → ℂ, IsTest f → IsTest (WeilMix.ptrB M ψ f) := by
  first | exact @GlobalTheory.JR.WeilMix.ptrB_isTest | exact GlobalTheory.JR.WeilMix.ptrB_isTest | (intros; apply GlobalTheory.JR.WeilMix.ptrB_isTest <;> assumption)
end _root_.GlobalTheory.T
