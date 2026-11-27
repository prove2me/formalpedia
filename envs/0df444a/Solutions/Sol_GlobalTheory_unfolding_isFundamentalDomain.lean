-- Prove2me | solution 1 for GlobalTheory.unfolding_isFundamentalDomain
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:44:19.252437+00:00
-- url     : https://prove2.me/submissions/313346a5-49d8-4e22-84ba-4e83c9f5973f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EncardSmulMemLeEncardSmulInterNonempty
import Theorems.Thm_GlobalTheory_setLIntegral_le_encard_mul_of_ae_covers
import Theorems.Thm_GlobalTheory_ae_exists_smul_mem_of_surjective
import Theorems.Thm_GlobalTheory_setLIntegral_le_mul_of_surjective
import Theorems.Thm_GlobalTheory_finiteIndex_map_of_surjective
import Theorems.Thm_GlobalTheory_setLIntegral_eq_index_map_mul
import Theorems.Thm_GlobalTheory_measure_eq_index_map_mul
import Theorems.Thm_GlobalTheory_setLAverage_eq_of_surjective
import Theorems.Thm_GlobalTheory_measure_le_measure_of_surjective

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
    {u : X → ℝ≥0∞} (hu : ∀ (g : G) (x : X), u (g • x) = u x) :
    (∀ B : Set X, NullMeasurableSet B μ → ∀ m : ℝ≥0∞,
      (∀ x, ({g : G | g • x ∈ B}.encard : ℝ≥0∞) ≤ m) →
        ∫⁻ x in B, u x ∂μ ≤ m * ∫⁻ x in D, u x ∂μ) ∧
    (∀ B : Set X, NullMeasurableSet B μ → ∫⁻ x in B, u x ∂μ
      ≤ ({g : G | (g • B ∩ B).Nonempty}.encard : ℝ≥0∞) * ∫⁻ x in D, u x ∂μ) ∧
    (Function.Surjective φ' → (∀ (k : K) (x : X), φ' k • x = k • x) →
      IsFundamentalDomain H' D' μ →
        μ D ≤ μ D' ∧ (K.FiniteIndex →
          (∃ n : ℕ, 0 < n ∧ n ∣ K.index ∧ μ D' = n * μ D ∧
            ∫⁻ x in D', u x ∂μ = n * ∫⁻ x in D, u x ∂μ) ∧
          ⨍⁻ x in D', u x ∂μ = ⨍⁻ x in D, u x ∂μ)) := by
  refine ⟨fun B hB m hm => setLIntegral_le_mul_of_surjective hφ hφs hD hB hu hm,
    fun B hB => setLIntegral_le_encard_mul_of_ae_covers
      (ae_exists_smul_mem_of_surjective hφ hφs hD) hB hu,
    fun hφ' hφs' hD' => ⟨measure_le_measure_of_surjective hφ hφs hD hφ' hφs' hD', fun _ =>
      ⟨⟨(K.map φ).index, ?_, K.index_map_dvd hφ, measure_eq_index_map_mul hφ hφs hD hφ' hφs' hD',
        setLIntegral_eq_index_map_mul hφ hφs hD hφ' hφs' hD' hu⟩,
        setLAverage_eq_of_surjective hφ hφs hD hφ' hφs' hD' hu⟩⟩⟩
  exact Nat.pos_of_ne_zero (finiteIndex_map_of_surjective (K := K) hφ).index_ne_zero
end GlobalTheory
