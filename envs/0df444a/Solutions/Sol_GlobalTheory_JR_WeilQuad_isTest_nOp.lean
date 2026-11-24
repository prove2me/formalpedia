-- Prove2me | solution 1 for GlobalTheory.JR.WeilQuad.isTest_nOp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:20:05.372399+00:00
-- url     : https://prove2.me/submissions/5b83fb04-edc7-4372-afa6-c1fd6909d582

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsStableGauss
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NonemptyMeasAndReps
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_QuadraticWeilUnipotentTorusPreserveTest
import Theorems.Thm_GlobalTheory_JR_WeilQuad_isLocallyConstant_of_stdChar
import Theorems.Thm_GlobalTheory_JR_EtMeas_continuous_NL


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
theorem _root_.solution [Unram F E] (A : Et F E) {ψ : AddChar F ℂ} (hψ : IsStdChar ψ) (x z : A.K) {φ : A.L → ℂ}
    (hφ : IsTest φ) : IsTest (nOp A ψ x z φ) := by
  have htr : Continuous (Algebra.trace F A.K) := IsModuleTopology.continuous_of_linearMap _
  have hc : Continuous fun y : A.L => Algebra.trace F A.K (z * x * A.NL y) :=
    htr.comp (continuous_const.mul (GlobalTheory.JR.EtMeas.continuous_NL A))
  have hl : IsLocallyConstant fun y : A.L => A.psiK ψ (z * x * A.NL y) :=
    (isLocallyConstant_of_stdChar hψ).comp_continuous hc
  exact ⟨hl.mul hφ.1, hφ.2.mul_left⟩
end GlobalTheory.JR.WeilQuad
