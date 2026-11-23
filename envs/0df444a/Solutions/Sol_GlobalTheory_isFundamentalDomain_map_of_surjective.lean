-- Prove2me | solution 1 for GlobalTheory.isFundamentalDomain_map_of_surjective
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:31:35.087301+00:00
-- url     : https://prove2.me/submissions/526b321c-7046-423d-9f87-769c219c5981

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
theorem _root_.solution (hφ : Function.Surjective φ)
    (hφs : ∀ (g : G) (x : X), φ g • x = g • x) (hD : IsFundamentalDomain H D μ)
    (hφ' : Function.Surjective φ') (hφs' : ∀ (k : K) (x : X), φ' k • x = k • x)
    (hD' : IsFundamentalDomain H' D' μ) : IsFundamentalDomain (K.map φ) D' μ where
  nullMeasurableSet := hD'.nullMeasurableSet
  ae_covers := by
    filter_upwards [ae_exists_smul_mem_of_surjective hφ' hφs' hD'] with x ⟨k, hk⟩
    refine ⟨⟨φ k, k, k.2, rfl⟩, ?_⟩
    rw [Subgroup.smul_def, hφs]
    exact hk
  aedisjoint := by
    have := measurableConstSMul_of_surjective hφ hφs
    have : SMulInvariantMeasure H X μ := smulInvariantMeasure_of_surjective hφ hφs
    have : Countable H := hφ.countable
    rintro ⟨_, k₁, hk₁, rfl⟩ ⟨_, k₂, hk₂, rfl⟩ hne
    have hne' : φ k₁ ≠ φ k₂ := fun h => hne (Subtype.ext h)
    have hset : ∀ (k : K) (S : Set X), φ k • S = φ' k • S := fun k S => by
      simp only [← image_smul, hφs, hφs', Subgroup.smul_def]
    by_cases hμ : μ = 0
    · simp [hμ, Function.onFun, AEDisjoint]
    have hne'' : φ' ⟨k₁, hk₁⟩ ≠ φ' ⟨k₂, hk₂⟩ := by
      intro h
      have h1 := hD.aedisjoint hne'
      have h2 : φ k₁ • D = φ k₂ • D := by
        rw [hset ⟨k₁, hk₁⟩, hset ⟨k₂, hk₂⟩, h]
      simp only [Function.onFun, AEDisjoint, h2, inter_self, measure_smul] at h1
      exact hD.measure_ne_zero hμ h1
    have h3 := hD'.aedisjoint hne''
    simp only [Function.onFun, ← hset] at h3
    exact h3
end GlobalTheory
