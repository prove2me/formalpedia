-- Prove2me | solution 1 for GlobalTheory.JR.WeilQuad.isTest_mOp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:20:04.320182+00:00
-- url     : https://prove2.me/submissions/f6fd07c6-69fc-4e41-a2a2-d757174162ff

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsStableGauss
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NonemptyMeasAndReps
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_QuadraticWeilUnipotentTorusPreserveTest

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.WeilQuad
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
namespace GlobalTheory.JR.WeilQuad
theorem _root_.solution (A : Et F E) (ω : A.K → ℂ) (s : A.Kˣ) {φ : A.L → ℂ} (hφ : IsTest φ) :
    IsTest (mOp A ω s φ) := by
  have h1 : IsTest (φ ∘ smulHomeo A s) :=
    ⟨hφ.1.comp_continuous (smulHomeo A s).continuous, hφ.2.comp_homeomorph _⟩
  exact ⟨(IsLocallyConstant.const (ω s * (A.absK s : ℂ))).mul h1.1, h1.2.mul_left⟩
end GlobalTheory.JR.WeilQuad
