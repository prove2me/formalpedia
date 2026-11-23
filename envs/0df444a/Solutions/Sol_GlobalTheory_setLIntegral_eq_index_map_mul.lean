-- Prove2me | solution 1 for GlobalTheory.setLIntegral_eq_index_map_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:34:32.686802+00:00
-- url     : https://prove2.me/submissions/020614cc-4b80-4802-b71c-37df9e05b429

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EncardSmulMemLeEncardSmulInterNonempty
import Theorems.Thm_GlobalTheory_setLIntegral_subgroup_eq_index_mul
import Theorems.Thm_GlobalTheory_measurableConstSMul_of_surjective
import Theorems.Thm_GlobalTheory_smulInvariantMeasure_of_surjective
import Theorems.Thm_GlobalTheory_isFundamentalDomain_map_of_surjective
import Theorems.Thm_GlobalTheory_finiteIndex_map_of_surjective

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
    (hD' : IsFundamentalDomain H' D' μ) {u : X → ℝ≥0∞}
    (hu : ∀ (g : G) (x : X), u (g • x) = u x) :
    ∫⁻ x in D', u x ∂μ = ((K.map φ).index : ℝ≥0∞) * ∫⁻ x in D, u x ∂μ := by
  have := measurableConstSMul_of_surjective hφ hφs
  have : SMulInvariantMeasure H X μ := smulInvariantMeasure_of_surjective hφ hφs
  have : Countable H := hφ.countable
  have := finiteIndex_map_of_surjective (K := K) hφ
  refine setLIntegral_subgroup_eq_index_mul hD
    (isFundamentalDomain_map_of_surjective hφ hφs hD hφ' hφs' hD') fun h x => ?_
  obtain ⟨g, rfl⟩ := hφ h
  rw [hφs, hu]
end GlobalTheory
