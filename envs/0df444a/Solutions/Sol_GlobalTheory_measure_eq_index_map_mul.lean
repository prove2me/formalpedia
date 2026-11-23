-- Prove2me | solution 1 for GlobalTheory.measure_eq_index_map_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:53:49.710361+00:00
-- url     : https://prove2.me/submissions/19d9e5dc-68e7-4fbb-a818-e511423e7d91

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
import Theorems.Thm_GlobalTheory_setIntegral_subgroup_eq_index_smul
import Theorems.Thm_GlobalTheory_setAverage_subgroup_eq
import Theorems.Thm_GlobalTheory_measurableConstSMul_of_surjective
import Theorems.Thm_GlobalTheory_smulInvariantMeasure_of_surjective
import Theorems.Thm_GlobalTheory_ae_exists_smul_mem_of_surjective
import Theorems.Thm_GlobalTheory_setLIntegral_le_mul_of_surjective
import Theorems.Thm_GlobalTheory_isFundamentalDomain_map_of_surjective
import Theorems.Thm_GlobalTheory_finiteIndex_map_of_surjective
import Theorems.Thm_GlobalTheory_setLIntegral_eq_index_map_mul

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
variable {G H X : Type*} [Group G] [Group H] [MulAction G X] [MulAction H X] [MeasurableSpace X]
  {μ : Measure X} {B D D' : Set X} {φ : G →* H}
variable [MeasurableConstSMul G X] [SMulInvariantMeasure G X μ] [Countable G]
variable {K : Subgroup G} {H' : Type*} [Group H'] [MulAction H' X] {φ' : K →* H'}
namespace GlobalTheory
theorem _root_.solution [K.FiniteIndex] (hφ : Function.Surjective φ)
    (hφs : ∀ (g : G) (x : X), φ g • x = g • x) (hD : IsFundamentalDomain H D μ)
    (hφ' : Function.Surjective φ') (hφs' : ∀ (k : K) (x : X), φ' k • x = k • x)
    (hD' : IsFundamentalDomain H' D' μ) : μ D' = ((K.map φ).index : ℝ≥0∞) * μ D := by
  simpa using setLIntegral_eq_index_map_mul hφ hφs hD hφ' hφs' hD' (u := fun _ => 1)
    (fun _ _ => rfl)
end GlobalTheory
