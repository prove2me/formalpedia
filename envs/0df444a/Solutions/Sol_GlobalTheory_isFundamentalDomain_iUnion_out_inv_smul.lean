-- Prove2me | solution 1 for GlobalTheory.isFundamentalDomain_iUnion_out_inv_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:40:05.255908+00:00
-- url     : https://prove2.me/submissions/4e12ecab-d80d-49b8-a6bc-9f5cb3ac46cf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EncardSmulMemLeEncardSmulInterNonempty
import Theorems.Thm_GlobalTheory_encard_smul_mem_le_encard_smul_inter_nonempty
import Theorems.Thm_GlobalTheory_tsum_indicator_smul_eq_encard
import Theorems.Thm_GlobalTheory_sum_restrict_preimage_smul_le
import Theorems.Thm_GlobalTheory_setLIntegral_le_mul_of_ae_covers
import Theorems.Thm_GlobalTheory_setIntegral_le_mul_of_ae_covers
import Theorems.Thm_GlobalTheory_setLIntegral_le_mul_of_isFundamentalDomain
import Theorems.Thm_GlobalTheory_setLIntegral_le_encard_mul_of_ae_covers
import Theorems.Thm_GlobalTheory_ae_encard_smul_mem_le_one
import Theorems.Thm_GlobalTheory_setLIntegral_le_of_isFundamentalDomain_of_ae_covers
import Theorems.Thm_GlobalTheory_measure_le_of_isFundamentalDomain_of_ae_covers
import Theorems.Thm_GlobalTheory_pairwise_aedisjoint_out_inv_smul

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
    (K : Subgroup G) : IsFundamentalDomain K (⋃ q : G ⧸ K, (q.out)⁻¹ • D) μ where
  nullMeasurableSet := by
    have : Countable (G ⧸ K) := QuotientGroup.mk_surjective.countable
    exact .iUnion fun q => hD.nullMeasurableSet_smul _
  ae_covers := by
    filter_upwards [hD.ae_covers] with x ⟨g, hg⟩
    have hk : ((g : G ⧸ K).out)⁻¹ * g ∈ K := QuotientGroup.eq.1 (QuotientGroup.out_eq' _)
    refine ⟨⟨_, hk⟩, mem_iUnion.2 ⟨(g : G ⧸ K), g • x, hg, ?_⟩⟩
    simp [Subgroup.smul_def, smul_smul]
  aedisjoint := by
    have : Countable (G ⧸ K) := QuotientGroup.mk_surjective.countable
    intro k₁ k₂ hk
    simp only [Function.onFun, Subgroup.smul_def, smul_set_iUnion, smul_smul]
    refine AEDisjoint.iUnion_left_iff.2 fun q₁ => AEDisjoint.iUnion_right_iff.2 fun q₂ => ?_
    refine hD.aedisjoint fun h => hk ?_
    have hq : q₁ = q₂ := by
      rw [← q₁.out_eq, ← q₂.out_eq]
      refine QuotientGroup.eq.2 ?_
      have : (q₁.out)⁻¹ * q₂.out = (k₁ : G)⁻¹ * k₂ := by
        rw [eq_inv_mul_iff_mul_eq, ← mul_assoc, h, inv_mul_cancel_right]
      rw [this]
      exact K.mul_mem (K.inv_mem k₁.2) k₂.2
    subst hq
    exact Subtype.ext (mul_right_cancel h)
end GlobalTheory
