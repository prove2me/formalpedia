-- Prove2me | solution 1 for GlobalTheory.setAverage_subgroup_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:19:04.294923+00:00
-- url     : https://prove2.me/submissions/23ef34e3-7cb0-4a1e-8f24-f8201d44eb59

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EncardSmulMemLeEncardSmulInterNonempty
import Theorems.Thm_GlobalTheory_measure_subgroup_eq_index_mul
import Theorems.Thm_GlobalTheory_setIntegral_subgroup_eq_index_smul

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
variable {E : Type*} [NormedAddCommGroup E]
variable [NormedSpace ℝ E]
namespace GlobalTheory
theorem _root_.solution [K.FiniteIndex] (hD : IsFundamentalDomain G D μ)
    (hD' : IsFundamentalDomain K D' μ) {f : X → E}
    (hf : ∀ (g : G) (x : X), f (g • x) = f x) :
    ⨍ x in D', f x ∂μ = ⨍ x in D, f x ∂μ := by
  have h0 : (K.index : ℝ) ≠ 0 := by exact_mod_cast Subgroup.FiniteIndex.index_ne_zero
  rw [setAverage_eq, setAverage_eq, setIntegral_subgroup_eq_index_smul hD hD' hf, smul_smul,
    measureReal_def, measureReal_def, measure_subgroup_eq_index_mul hD hD', ENNReal.toReal_mul,
    ENNReal.toReal_natCast, mul_inv, mul_right_comm, inv_mul_cancel₀ h0, one_mul]
end GlobalTheory
