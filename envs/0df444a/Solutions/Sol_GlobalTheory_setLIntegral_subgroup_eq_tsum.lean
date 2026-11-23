-- Prove2me | solution 1 for GlobalTheory.setLIntegral_subgroup_eq_tsum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:44:07.434676+00:00
-- url     : https://prove2.me/submissions/24166b3e-3a72-4cf8-9006-9e85ce0769a6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EncardSmulMemLeEncardSmulInterNonempty
import Theorems.Thm_GlobalTheory_pairwise_aedisjoint_out_inv_smul
import Theorems.Thm_GlobalTheory_isFundamentalDomain_iUnion_out_inv_smul

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
theorem _root_.solution (hD : IsFundamentalDomain G D μ)
    (hD' : IsFundamentalDomain K D' μ) {u : X → ℝ≥0∞}
    (hu : ∀ (g : G) (x : X), u (g • x) = u x) :
    ∫⁻ x in D', u x ∂μ = ∑' _ : G ⧸ K, ∫⁻ x in D, u x ∂μ := by
  have : Countable (G ⧸ K) := QuotientGroup.mk_surjective.countable
  rw [hD'.setLIntegral_eq (isFundamentalDomain_iUnion_out_inv_smul hD K) u fun k x => hu k x,
    lintegral_iUnion₀ (fun q => hD.nullMeasurableSet_smul _)
      (pairwise_aedisjoint_out_inv_smul hD K)]
  exact tsum_congr fun q => (hD.smul _).setLIntegral_eq hD u hu
end GlobalTheory
