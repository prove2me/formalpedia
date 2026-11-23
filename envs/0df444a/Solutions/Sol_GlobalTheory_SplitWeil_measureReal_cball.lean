-- Prove2me | solution 1 for GlobalTheory.SplitWeil.measureReal_cball
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:56:45.718946+00:00
-- url     : https://prove2.me/submissions/b710c2b9-0002-4409-b139-1b155c556abe

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Theorems.Thm_GlobalTheory_SplitWeil_measure_cball

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped NNReal ENNReal Pointwise Topology
noncomputable section
open GlobalTheory GlobalTheory.SplitWeil
variable (k : Type*) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {k}
variable [MeasurableSpace k] [BorelSpace k]
namespace GlobalTheory.SplitWeil
theorem _root_.solution (ν : Measure k) [ν.IsAddHaarMeasure] (s : kˣ) :
    ν.real (cball s) = nabs k s * ν.real (𝒪[k] : Set k) := by
  simp [Measure.real, measure_cball, nabs]
end GlobalTheory.SplitWeil
