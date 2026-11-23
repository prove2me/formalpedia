-- Prove2me | solution 1 for GlobalTheory.Wick.contraction_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:53:59.63642+00:00
-- url     : https://prove2.me/submissions/0afa79cc-4cf5-4174-8d81-a08e95a5f6e1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_WeightAddLeOfMemSupportDividedContraction
import Theorems.Thm_GlobalTheory_Wick_contraction_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open GlobalTheory GlobalTheory.Wick
variable {R S : Type*} [CommSemiring R] [CommSemiring S] {ι κ : Type*}
variable [Fintype κ]
variable [Fintype ι]
namespace GlobalTheory.Wick
theorem _root_.solution (γ : ι → κ → R) :
    contraction γ = ∑ i, (pderiv (Sum.inl i)).toLinearMap * rowContraction γ i := by
  refine LinearMap.ext fun P => ?_
  simp [contraction_apply, rowContraction_apply, LinearMap.sum_apply]
end GlobalTheory.Wick
