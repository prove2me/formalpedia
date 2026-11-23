-- Prove2me | solution 1 for GlobalTheory.SplitWeil.add_mem_cball
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:16:48.497797+00:00
-- url     : https://prove2.me/submissions/00fa562d-2342-491c-ae35-d63d5f406c66

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
theorem _root_.solution {s : kˣ} {x y : k} (hx : x ∈ cball s) (hy : y ∈ cball s) : x + y ∈ cball s := by
  rw [cball, Set.mem_setOf_eq] at *
  exact Valuation.map_add_le _ hx hy
end GlobalTheory.SplitWeil
