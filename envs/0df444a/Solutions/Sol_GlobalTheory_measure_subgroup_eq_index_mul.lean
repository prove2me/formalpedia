-- Prove2me | solution 1 for GlobalTheory.measure_subgroup_eq_index_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:54:41.862112+00:00
-- url     : https://prove2.me/submissions/4f86fde2-c1b2-4e64-b0a6-ec9f99b59526

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
    (hD' : IsFundamentalDomain K D' μ) : μ D' = (K.index : ℝ≥0∞) * μ D := by
  simpa using setLIntegral_subgroup_eq_index_mul hD hD' (u := fun _ => 1) (fun _ _ => rfl)
end GlobalTheory
