-- Prove2me | solution 1 for GlobalTheory.setLAverage_subgroup_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:01:57.271968+00:00
-- url     : https://prove2.me/submissions/e068d4d7-0ad5-4116-98f6-2dab9d81012a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EncardSmulMemLeEncardSmulInterNonempty
import Theorems.Thm_GlobalTheory_setLIntegral_subgroup_eq_index_mul
import Theorems.Thm_GlobalTheory_measure_subgroup_eq_index_mul

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
variable {G X : Type*} [Group G] [MulAction G X] [MeasurableSpace X] {μ : Measure X}
  [MeasurableConstSMul G X] [SMulInvariantMeasure G X μ] [Countable G] {D D' : Set X}
  {K : Subgroup G}
namespace GlobalTheory
theorem _root_.solution [K.FiniteIndex] (hD : IsFundamentalDomain G D μ)
    (hD' : IsFundamentalDomain K D' μ) {u : X → ℝ≥0∞}
    (hu : ∀ (g : G) (x : X), u (g • x) = u x) :
    ⨍⁻ x in D', u x ∂μ = ⨍⁻ x in D, u x ∂μ := by
  rw [setLAverage_eq, setLAverage_eq, setLIntegral_subgroup_eq_index_mul hD hD' hu,
    measure_subgroup_eq_index_mul hD hD', ENNReal.mul_div_mul_left]
  · exact_mod_cast Subgroup.FiniteIndex.index_ne_zero
  · exact ENNReal.natCast_ne_top _
end GlobalTheory
