-- Prove2me | solution 1 for GlobalTheory.integrableOn_subgroup_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:05:34.464652+00:00
-- url     : https://prove2.me/submissions/35d9e87c-8fe4-47ea-8be5-a1b1b90c6a60

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
namespace GlobalTheory
theorem _root_.solution [K.FiniteIndex] (hD : IsFundamentalDomain G D μ)
    (hD' : IsFundamentalDomain K D' μ) {f : X → E}
    (hf : ∀ (g : G) (x : X), f (g • x) = f x) : IntegrableOn f D' μ ↔ IntegrableOn f D μ := by
  rw [hD'.integrableOn_iff (isFundamentalDomain_iUnion_out_inv_smul hD K) fun k x => hf k x,
    integrableOn_finite_iUnion]
  simp only [fun g : G => (hD.smul g).integrableOn_iff hD hf, forall_const]
end GlobalTheory
