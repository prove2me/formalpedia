-- Prove2me | solution 1 for GlobalTheory.setLAverage_eq_of_surjective
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:57:18.11366+00:00
-- url     : https://prove2.me/submissions/757f2630-bd76-48c6-bfaf-1a13427b9eee

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EncardSmulMemLeEncardSmulInterNonempty
import Theorems.Thm_GlobalTheory_finiteIndex_map_of_surjective
import Theorems.Thm_GlobalTheory_setLIntegral_eq_index_map_mul
import Theorems.Thm_GlobalTheory_measure_eq_index_map_mul

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
    ⨍⁻ x in D', u x ∂μ = ⨍⁻ x in D, u x ∂μ := by
  have := finiteIndex_map_of_surjective (K := K) hφ
  rw [setLAverage_eq, setLAverage_eq, setLIntegral_eq_index_map_mul hφ hφs hD hφ' hφs' hD' hu,
    measure_eq_index_map_mul hφ hφs hD hφ' hφs' hD', ENNReal.mul_div_mul_left]
  · exact_mod_cast Subgroup.FiniteIndex.index_ne_zero
  · exact ENNReal.natCast_ne_top _
end GlobalTheory
