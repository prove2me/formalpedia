-- Prove2me | solution 1 for GlobalTheory.setAverage_eq_of_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:41:03.846274+00:00
-- url     : https://prove2.me/submissions/f8397c19-a6ac-4882-84a2-a90348d99032

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EncardSmulMemLeEncardSmulInterNonempty
import Theorems.Thm_GlobalTheory_integrableOn_subgroup_iff
import Theorems.Thm_GlobalTheory_setIntegral_subgroup_eq_index_smul
import Theorems.Thm_GlobalTheory_setAverage_subgroup_eq
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
    (hD' : IsFundamentalDomain H' D' μ) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : X → E} (hf : ∀ (g : G) (x : X), f (g • x) = f x) :
    (IntegrableOn f D' μ ↔ IntegrableOn f D μ) ∧
      ∫ x in D', f x ∂μ = ((K.map φ).index : ℝ) • ∫ x in D, f x ∂μ ∧
      ⨍ x in D', f x ∂μ = ⨍ x in D, f x ∂μ := by
  have := measurableConstSMul_of_surjective hφ hφs
  have : SMulInvariantMeasure H X μ := smulInvariantMeasure_of_surjective hφ hφs
  have : Countable H := hφ.countable
  have := finiteIndex_map_of_surjective (K := K) hφ
  have hD'' := isFundamentalDomain_map_of_surjective hφ hφs hD hφ' hφs' hD'
  have hf' : ∀ (h : H) (x : X), f (h • x) = f x := fun h x => by
    obtain ⟨g, rfl⟩ := hφ h
    rw [hφs, hf]
  exact ⟨integrableOn_subgroup_iff hD hD'' hf', setIntegral_subgroup_eq_index_smul hD hD'' hf',
    setAverage_subgroup_eq hD hD'' hf'⟩
end GlobalTheory
