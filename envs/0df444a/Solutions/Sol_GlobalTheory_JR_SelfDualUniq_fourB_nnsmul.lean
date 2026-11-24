-- Prove2me | solution 1 for GlobalTheory.JR.SelfDualUniq.fourB_nnsmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:09:43.043836+00:00
-- url     : https://prove2.me/submissions/76a72a4b-5e41-45d2-8b1d-531ece72a5ab

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsSelfDualOfDualSubgroups
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsSmallDualLattices
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NonemptyMeasAndReps
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SelfDualMeasureExistsUniqueFourierInversion

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.SelfDualUniq
variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [MeasurableSpace V]
namespace GlobalTheory.JR.SelfDualUniq
theorem _root_.solution (μ : Measure V) (c : NNReal) (B : V → V → ℂ) (f : V → ℂ) (y : V) :
    fourB (c • μ) B f y = ((c : ℝ) : ℂ) * fourB μ B f y := by
  simp only [fourB, integral_smul_nnreal_measure]
  rw [NNReal.smul_def, Complex.real_smul]
end GlobalTheory.JR.SelfDualUniq
