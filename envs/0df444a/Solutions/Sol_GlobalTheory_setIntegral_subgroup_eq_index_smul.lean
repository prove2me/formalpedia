-- Prove2me | solution 1 for GlobalTheory.setIntegral_subgroup_eq_index_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:15:21.808708+00:00
-- url     : https://prove2.me/submissions/4fed69a6-1bd8-42b7-b8ce-87f60bd4cad3

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
import Theorems.Thm_GlobalTheory_isFundamentalDomain_iUnion_out_inv_smul
import Theorems.Thm_GlobalTheory_setLIntegral_subgroup_eq_tsum
import Theorems.Thm_GlobalTheory_setLIntegral_subgroup_eq_index_mul
import Theorems.Thm_GlobalTheory_measure_subgroup_eq_index_mul
import Theorems.Thm_GlobalTheory_setLAverage_subgroup_eq
import Theorems.Thm_GlobalTheory_measure_le_measure_subgroup
import Theorems.Thm_GlobalTheory_integrableOn_subgroup_iff

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
    ∫ x in D', f x ∂μ = (K.index : ℝ) • ∫ x in D, f x ∂μ := by
  by_cases hi : IntegrableOn f D μ
  · have := Fintype.ofFinite (G ⧸ K)
    have hE := isFundamentalDomain_iUnion_out_inv_smul hD K
    rw [hD'.setIntegral_eq hE fun k x => hf k x,
      integral_iUnion_ae (fun q => hD.nullMeasurableSet_smul _)
        (pairwise_aedisjoint_out_inv_smul hD K) ((integrableOn_subgroup_iff hD hE hf).2 hi)]
    simp only [fun g : G => (hD.smul g).setIntegral_eq hD hf]
    rw [tsum_fintype, Finset.sum_const, Subgroup.index, Nat.card_eq_fintype_card,
      Finset.card_univ, Nat.cast_smul_eq_nsmul]
  · rw [integral_undef hi, integral_undef (mt (integrableOn_subgroup_iff hD hD' hf).1 hi),
      smul_zero]
end GlobalTheory
