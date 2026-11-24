-- Prove2me | solution 1 for GlobalTheory.JR.MeasScale.fourB_twice_nnreal_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:01:20.465802+00:00
-- url     : https://prove2.me/submissions/8abd86f3-abe6-4ebc-8a0c-0fd3c68e0528

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NonemptyMeasAndReps
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_QuadraticStarStructure
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DistribHaarCharTransport
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FiniteNormedAlgebraEqModuleTopology
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsSelfDualMeasuresAndAbsKScale
import Theorems.Thm_GlobalTheory_JR_MeasScale_fourB_nnreal_smul
import Theorems.Thm_GlobalTheory_JR_MeasScale_fourB_const_mul

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
    (f : V → ℂ) (y : V) :
    fourB (c • μ) B (fourB (c • μ) B f) y = (c : ℂ) ^ 2 * fourB μ B (fourB μ B f) y := by
  have h : fourB (c • μ) B f = fun z => (c : ℂ) * fourB μ B f z :=
    funext fun z => fourB_nnreal_smul μ c B f z
  rw [fourB_nnreal_smul, h, fourB_const_mul]
  ring
end GlobalTheory.JR.MeasScale
