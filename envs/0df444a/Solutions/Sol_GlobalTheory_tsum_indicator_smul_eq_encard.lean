-- Prove2me | solution 1 for GlobalTheory.tsum_indicator_smul_eq_encard
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:00:52.585166+00:00
-- url     : https://prove2.me/submissions/0f7d1019-ff89-425a-9ce4-8691d6dc8992

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EncardSmulMemLeEncardSmulInterNonempty
import Theorems.Thm_GlobalTheory_encard_smul_mem_le_encard_smul_inter_nonempty

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set
open scoped ENNReal Pointwise
open GlobalTheory
variable {G X : Type*} [Group G] [MulAction G X]
variable [MeasurableSpace X] {μ : Measure X} [MeasurableConstSMul G X]
  [SMulInvariantMeasure G X μ] [Countable G] {B D : Set X}
omit [MeasurableSpace X] [MeasurableConstSMul G X] [Countable G]
namespace GlobalTheory
theorem _root_.solution (B : Set X) (x : X) :
    ∑' g : G, ((fun y => g • y) ⁻¹' B).indicator (fun _ => (1 : ℝ≥0∞)) x
      = ({g : G | g • x ∈ B}.encard : ℝ≥0∞) := by
  rw [← ENNReal.tsum_set_one, tsum_subtype {g : G | g • x ∈ B} (fun _ => (1 : ℝ≥0∞))]
  refine tsum_congr fun g => ?_
  by_cases h : g • x ∈ B <;> simp [Set.indicator, h]
end GlobalTheory
