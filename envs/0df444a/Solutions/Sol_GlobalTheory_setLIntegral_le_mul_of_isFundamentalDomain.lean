-- Prove2me | solution 1 for GlobalTheory.setLIntegral_le_mul_of_isFundamentalDomain
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:14:04.401556+00:00
-- url     : https://prove2.me/submissions/970ae7c4-42f6-4f42-88c2-879b92a80cd3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EncardSmulMemLeEncardSmulInterNonempty
import Theorems.Thm_GlobalTheory_setLIntegral_le_mul_of_ae_covers

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
namespace GlobalTheory
theorem _root_.solution (hD : IsFundamentalDomain G D μ)
    (hB : NullMeasurableSet B μ) {u : X → ℝ≥0∞} (hu : ∀ (g : G) (x : X), u (g • x) = u x)
    {m : ℝ≥0∞} (hm : ∀ x, ({g : G | g • x ∈ B}.encard : ℝ≥0∞) ≤ m) :
    ∫⁻ x in B, u x ∂μ ≤ m * ∫⁻ x in D, u x ∂μ :=
  setLIntegral_le_mul_of_ae_covers hD.ae_covers hB hu (.of_forall hm)
end GlobalTheory
