-- Prove2me | solution 1 for GlobalTheory.T.quadraticWeilFourier_preserves_test_additive
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:08:07.316324+00:00
-- url     : https://prove2.me/submissions/3add79b3-736d-4dfc-af7d-ceb42eae7839

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_QuadraticWeilFourierPreservesTestAdditive
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsStableGauss
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_QuadraticWeilFourierPreservesTestAdditiveStatement
import Theorems.Thm_GlobalTheory_JR_WeilQuad_fOp_isTest_add


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (x : A.Kˣ) (μ : Measure A.L) (ω : A.K → ℂ), Hyp A ψ x μ ω → ∀ φ : A.L → ℂ, IsTest φ → IsTest (fOp A ψ x μ φ) ∧ ∀ φ' : A.L → ℂ, IsTest φ' → fOp A ψ x μ (φ + φ') = fOp A ψ x μ φ + fOp A ψ x μ φ' := by
  first | exact @GlobalTheory.JR.WeilQuad.fOp_isTest_add | exact GlobalTheory.JR.WeilQuad.fOp_isTest_add | (intros; apply GlobalTheory.JR.WeilQuad.fOp_isTest_add <;> assumption)
end _root_.GlobalTheory.T
