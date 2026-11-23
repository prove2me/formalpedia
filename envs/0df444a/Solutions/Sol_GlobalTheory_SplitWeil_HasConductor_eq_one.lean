-- Prove2me | solution 1 for GlobalTheory.SplitWeil.HasConductor.eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:47:37.345976+00:00
-- url     : https://prove2.me/submissions/c9b34e7b-415f-42d5-8af8-84f3231d571e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField

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
variable {ψ : AddChar k Circle} {c : kˣ}
namespace GlobalTheory.SplitWeil
namespace HasConductor
theorem _root_.solution (h : HasConductor ψ c) {y : k} (hy : y ∈ cball c) : ψ y = 1 :=
  (h c).mpr le_rfl y hy
end HasConductor
end GlobalTheory.SplitWeil
