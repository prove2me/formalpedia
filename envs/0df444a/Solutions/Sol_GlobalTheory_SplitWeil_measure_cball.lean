-- Prove2me | solution 1 for GlobalTheory.SplitWeil.measure_cball
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:53:18.374341+00:00
-- url     : https://prove2.me/submissions/205f6f53-0540-47af-b620-16e2020c6a14

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Theorems.Thm_GlobalTheory_SplitWeil_secondCountable
import Theorems.Thm_GlobalTheory_SplitWeil_t2Space
import Theorems.Thm_GlobalTheory_SplitWeil_cball_eq_smul

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
    ν (cball s) = distribHaarChar k s * ν (𝒪[k] : Set k) := by
  haveI := secondCountable k
  haveI := t2Space k
  rw [cball_eq_smul, distribHaarChar_mul]
end GlobalTheory.SplitWeil
