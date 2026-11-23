-- Prove2me | solution 1 for GlobalTheory.SplitWeil.mem_cball_uniformiser
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:55:13.193804+00:00
-- url     : https://prove2.me/submissions/1ac03252-6bd6-41f3-9162-084a7823e349

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
namespace GlobalTheory.SplitWeil
theorem _root_.solution {ϖ : 𝒪[k]} (hϖ : Irreducible ϖ) {x : kˣ} (hx : (x : k) = ϖ) (y : 𝒪[k]) :
    (y : k) ∈ cball x ↔ y ∈ 𝓂[k] := by
  rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton, cball, Set.mem_setOf_eq, hx]
  exact (Valuation.Integers.le_iff_dvd (Valuation.integer.integers (valuation k)))
end GlobalTheory.SplitWeil
