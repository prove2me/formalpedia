-- Prove2me | solution 1 for GlobalTheory.JR.MeasScale.fourB_nnreal_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:53:34.356716+00:00
-- url     : https://prove2.me/submissions/bd67cc74-650c-4207-9b43-1b8b37556cdb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NonemptyMeasAndReps
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_QuadraticStarStructure
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DistribHaarCharTransport
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FiniteNormedAlgebraEqModuleTopology
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsSelfDualMeasuresAndAbsKScale

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open scoped Pointwise NNReal ENNReal
noncomputable section
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.MeasScale
namespace GlobalTheory.JR.MeasScale
theorem _root_.solution {V : Type} [MeasurableSpace V] (μ : Measure V) (c : ℝ≥0) (B : V → V → ℂ)
    (f : V → ℂ) (y : V) : fourB (c • μ) B f y = (c : ℂ) * fourB μ B f y := by
  simp only [fourB]
  rw [integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]
end GlobalTheory.JR.MeasScale
