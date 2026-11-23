-- Prove2me | solution 1 for GlobalTheory.pairwise_aedisjoint_out_inv_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:57:33.857798+00:00
-- url     : https://prove2.me/submissions/364a149b-a171-4aca-8f36-7e10e6d025c9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EncardSmulMemLeEncardSmulInterNonempty

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
omit [Countable G] [MeasurableConstSMul G X] [SMulInvariantMeasure G X μ]
namespace GlobalTheory
theorem _root_.solution (hD : IsFundamentalDomain G D μ) (K : Subgroup G) :
    Pairwise (Function.onFun (AEDisjoint μ) fun q : G ⧸ K => (q.out)⁻¹ • D) := by
  intro q₁ q₂ h
  refine hD.aedisjoint fun h' => h ?_
  rw [← q₁.out_eq, ← q₂.out_eq, inv_injective h']
end GlobalTheory
