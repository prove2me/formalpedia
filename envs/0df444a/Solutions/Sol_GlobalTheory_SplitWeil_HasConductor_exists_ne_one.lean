-- Prove2me | solution 1 for GlobalTheory.SplitWeil.HasConductor.exists_ne_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:55:45.372804+00:00
-- url     : https://prove2.me/submissions/720bd2e0-775c-4a58-9ec9-125d0aa242e4

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
theorem _root_.solution (h : HasConductor ψ c) (s : kˣ) {x : k} (hx : x ∉ cball (c * s⁻¹)) :
    ∃ t ∈ cball s, ψ (t * x) ≠ 1 := by
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact hx (by simp [cball])
  by_contra hne
  push Not at hne
  apply hx
  have h1 := (h (s * x)).mp fun y hy => by
    have := hne (y * x⁻¹) (by
      rw [cball, Set.mem_setOf_eq, map_mul, map_inv₀, mul_inv_le_iff₀ (by simp [zero_lt_iff, hx0]), ← map_mul]
      exact hy)
    rwa [inv_mul_cancel_right₀ hx0] at this
  rw [cball, Set.mem_setOf_eq, Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀,
    le_mul_inv_iff₀ (by simp [zero_lt_iff]), mul_comm, ← map_mul]
  exact h1
end HasConductor
end GlobalTheory.SplitWeil
