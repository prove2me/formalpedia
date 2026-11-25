-- Prove2me | solution 1 for GlobalTheory.T.weilRep_evalZero_mem_induced
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:08:45.120511+00:00
-- url     : https://prove2.me/submissions/ffa3b37e-0ff9-4a70-b0df-64bd004ddd84

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WeilRepEvalZeroMemInduced
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WeilRepEvalZeroMemInducedStatement
import Theorems.Thm_GlobalTheory_WeilSmooth_jx_mem_induced


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
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (x : A.Kˣ) (μ : Measure A.L) (γ : ℂ) W, A.IsWeil ψ x A.etaK μ γ W → ∀ φ, IsTest φ → A.InI (fun g => W g φ 0) ∧ (φ ≠ 0 → γ ≠ 0) := by
  first | exact @GlobalTheory.WeilSmooth.jx_mem_induced | exact GlobalTheory.WeilSmooth.jx_mem_induced | (intros; apply GlobalTheory.WeilSmooth.jx_mem_induced <;> assumption)
end _root_.GlobalTheory.T
