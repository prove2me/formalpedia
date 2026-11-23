-- Prove2me | solution 1 for GlobalTheory.setLIntegral_subgroup_eq_index_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:48:00.961874+00:00
-- url     : https://prove2.me/submissions/ad5aaef1-d644-4cc8-b354-bd1db92abbd8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EncardSmulMemLeEncardSmulInterNonempty
import Theorems.Thm_GlobalTheory_setLIntegral_subgroup_eq_tsum

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
    ∫⁻ x in D', u x ∂μ = (K.index : ℝ≥0∞) * ∫⁻ x in D, u x ∂μ := by
  have := Fintype.ofFinite (G ⧸ K)
  rw [setLIntegral_subgroup_eq_tsum hD hD' hu, tsum_fintype, Finset.sum_const, nsmul_eq_mul,
    Subgroup.index, Nat.card_eq_fintype_card, Finset.card_univ]
end GlobalTheory
