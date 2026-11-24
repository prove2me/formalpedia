-- Prove2me | solution 1 for GlobalTheory.T.quadraticWeilFourier_comp_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:21:18.379851+00:00
-- url     : https://prove2.me/submissions/52cf486f-b2f5-42b6-a1f5-ee47a8fa0a57

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_QuadraticWeilFourierCompSmul
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsStableGauss
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_QuadraticWeilFourierCompSmulStatement
import Theorems.Thm_GlobalTheory_JR_WeilQuad_fOp_comp_smul


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
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (x : A.Kˣ) (μ : Measure A.L) (ω : A.K → ℂ), Hyp A ψ x μ ω → ∀ (s : A.Kˣ) (φ : A.L → ℂ), IsTest φ → ∀ y, fOp A ψ x μ (fun y' => φ ((s : A.K) • y')) y = ((A.absK s : ℂ) ^ 2)⁻¹ * fOp A ψ x μ φ (((s⁻¹ : A.Kˣ) : A.K) • y) := by
  first | exact @GlobalTheory.JR.WeilQuad.fOp_comp_smul | exact GlobalTheory.JR.WeilQuad.fOp_comp_smul | (intros; apply GlobalTheory.JR.WeilQuad.fOp_comp_smul <;> assumption)
end _root_.GlobalTheory.T
