-- Prove2me | solution 1 for GlobalTheory.JR.MeasScale.fourB_const_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:53:08.428104+00:00
-- url     : https://prove2.me/submissions/6ed72b8f-ef22-4ac8-9deb-66de1fb11db6

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
theorem _root_.solution {V : Type} [MeasurableSpace V] (μ : Measure V) (a : ℂ) (B : V → V → ℂ)
    (g : V → ℂ) (y : V) : fourB μ B (fun z => a * g z) y = a * fourB μ B g y := by
  simp only [fourB, mul_assoc]
  exact integral_const_mul a _
end GlobalTheory.JR.MeasScale
