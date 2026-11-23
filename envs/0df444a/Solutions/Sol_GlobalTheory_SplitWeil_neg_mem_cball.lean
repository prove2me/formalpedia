-- Prove2me | solution 1 for GlobalTheory.SplitWeil.neg_mem_cball
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:47:38.163202+00:00
-- url     : https://prove2.me/submissions/071d3ecc-243c-4af6-b7f6-9b386f7786dc

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
theorem _root_.solution {s : kˣ} {x : k} (hx : x ∈ cball s) : -x ∈ cball s := by
  simpa [cball] using hx
end GlobalTheory.SplitWeil
