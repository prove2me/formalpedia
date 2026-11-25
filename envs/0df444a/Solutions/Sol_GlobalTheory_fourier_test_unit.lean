-- Prove2me | solution 1 for GlobalTheory.fourier_test_unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:52:42.145305+00:00
-- url     : https://prove2.me/submissions/5b3c36ba-415b-48d3-873f-c0cf1d29aaa4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsNhdsZeroTranslationInvariantOfLocallyConstStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitIndicatorGLBlockIsLocallyConstantCompactSuppStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsTestUnitIndicatorHermitianBlockStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocallyConstantPartialFourierGLBlockStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_HasCompactSupportPartialFourierGLBlockStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_PartialFourierHermitianBlockIsLocallyConstantStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_PartialFourierHermitianBlockHasCompactSupportStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_PartialFourierGLBlockUnitIndicatorStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_PartialFourierHermitianBlockUnitIndicatorStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedQuadraticTraceEqAddStarStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsIntegralTraceUnitUnramifiedQuadraticStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_PartialFourierPreservesTestFixesUnit
import Theorems.Thm_GlobalTheory_T_exists_integral_trace_unit_unramifiedQuadratic
import Theorems.Thm_GlobalTheory_T_exists_nhds_zero_translation_invariant_of_locallyConstant
import Theorems.Thm_GlobalTheory_T_hasCompactSupport_partialFourierGLBlock
import Theorems.Thm_GlobalTheory_T_isLocallyConstant_partialFourierGLBlock
import Theorems.Thm_GlobalTheory_T_isTest_unitIndicatorHermitianBlock
import Theorems.Thm_GlobalTheory_T_partialFourierGLBlock_unitIndicator
import Theorems.Thm_GlobalTheory_T_partialFourierHermitianBlock_hasCompactSupport
import Theorems.Thm_GlobalTheory_T_partialFourierHermitianBlock_isLocallyConstant
import Theorems.Thm_GlobalTheory_T_partialFourierHermitianBlock_unitIndicator
import Theorems.Thm_GlobalTheory_T_unitIndicatorGLBlock_isLocallyConstantCompactSupport
import Theorems.Thm_GlobalTheory_T_unramifiedQuadratic_trace_eq_add_star


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (M : Meas r F E) (ψ : AddChar F ℂ), IsStdChar ψ → (∀ f', IsTest f' → IsTest (fourG M ψ f')) ∧ (∀ f, IsTest f → IsTest (fourU M ψ f)) ∧ IsTest (unitG r F) ∧ IsTest (unitU r F E) ∧ fourG M ψ (unitG r F) = unitG r F ∧ fourU M ψ (unitU r F E) = unitU r F E := by
  intro F E _ _ _ _ hU r M ψ hψ
  haveI := hU.ultraF; haveI := hU.ultraE; haveI := hU.lcF; haveI := hU.lcE
  have htr := GlobalTheory.T.unramifiedQuadratic_trace_eq_add_star F E
  refine ⟨fun f' hf => ⟨GlobalTheory.T.isLocallyConstant_partialFourierGLBlock F E r M ψ hψ f' hf (GlobalTheory.T.exists_nhds_zero_translation_invariant_of_locallyConstant _ f' hf), GlobalTheory.T.hasCompactSupport_partialFourierGLBlock F E r M ψ hψ f' hf (GlobalTheory.T.exists_nhds_zero_translation_invariant_of_locallyConstant _ f' hf)⟩,
    fun f hf => ⟨GlobalTheory.T.partialFourierHermitianBlock_isLocallyConstant F E r M ψ hψ htr f hf (GlobalTheory.T.exists_nhds_zero_translation_invariant_of_locallyConstant _ f hf), GlobalTheory.T.partialFourierHermitianBlock_hasCompactSupport F E r M ψ hψ htr f hf (GlobalTheory.T.exists_nhds_zero_translation_invariant_of_locallyConstant _ f hf)⟩,
    GlobalTheory.T.unitIndicatorGLBlock_isLocallyConstantCompactSupport F r, GlobalTheory.T.isTest_unitIndicatorHermitianBlock F E r hU.norm_star, GlobalTheory.T.partialFourierGLBlock_unitIndicator F E r M ψ hψ, GlobalTheory.T.partialFourierHermitianBlock_unitIndicator F E r M ψ hψ htr (GlobalTheory.T.exists_integral_trace_unit_unramifiedQuadratic F E htr)⟩
end GlobalTheory
