-- Prove2me | solution 1 for GlobalTheory.SplitWeil.HasConductor.ne_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:04:37.614386+00:00
-- url     : https://prove2.me/submissions/b3587c1f-39b1-488e-beb4-108f93560b48

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
theorem _root_.solution (h : HasConductor ψ c) : ψ ≠ 1 := by
  rintro rfl
  obtain ⟨r, hr, hr1⟩ := Valuation.IsNontrivial.exists_lt_one (v := valuation k)
  have hr0 : r ≠ 0 := by simpa using hr
  have h1 := (h (r⁻¹ * c)).mp fun y _ => by simp
  rw [map_mul, map_inv₀, inv_mul_le_iff₀ (by simp [zero_lt_iff, hr0])] at h1
  exact absurd (mul_lt_of_lt_one_left (by simp [zero_lt_iff]) hr1) (not_lt.mpr h1)
end HasConductor
end GlobalTheory.SplitWeil
