-- Prove2me | solution 1 for GlobalTheory.SplitWeil.cball_eq_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:47:37.52627+00:00
-- url     : https://prove2.me/submissions/97b7e56b-67bf-460c-a36d-e339dfa0c1c3

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
theorem _root_.solution (s : kˣ) : cball s = s • (𝒪[k] : Set k) := by
  ext x
  rw [Set.mem_smul_set_iff_inv_smul_mem]
  simp only [cball, Set.mem_setOf_eq, SetLike.mem_coe, Valuation.mem_integer_iff, Units.smul_def,
    smul_eq_mul, map_mul, Units.val_inv_eq_inv_val, map_inv₀]
  rw [inv_mul_le_iff₀ (by simp [zero_lt_iff]), mul_one]
end GlobalTheory.SplitWeil
