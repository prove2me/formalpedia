-- Prove2me | solution 1 for GlobalTheory.setLIntegral_le_mul_of_range_toPermHom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:41:11.557939+00:00
-- url     : https://prove2.me/submissions/fe6f5480-cd6e-440a-8698-16f07f2b72e8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EncardSmulMemLeEncardSmulInterNonempty
import Theorems.Thm_GlobalTheory_setLIntegral_le_mul_of_surjective

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
  [MeasurableConstSMul G X] [SMulInvariantMeasure G X μ] [Countable G] {B D D' : Set X}
  {K : Subgroup G}
namespace GlobalTheory
theorem _root_.solution
    (hD : IsFundamentalDomain (MulAction.toPermHom G X).range D μ)
    (hB : NullMeasurableSet B μ) {u : X → ℝ≥0∞} (hu : ∀ (g : G) (x : X), u (g • x) = u x)
    {m : ℝ≥0∞} (hm : ∀ x, ({g : G | g • x ∈ B}.encard : ℝ≥0∞) ≤ m) :
    ∫⁻ x in B, u x ∂μ ≤ m * ∫⁻ x in D, u x ∂μ :=
  setLIntegral_le_mul_of_surjective (MulAction.toPermHom G X).rangeRestrict_surjective
    (fun _ _ => rfl) hD hB hu hm
end GlobalTheory
