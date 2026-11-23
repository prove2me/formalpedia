-- Prove2me | solution 1 for GlobalTheory.Wick.contraction_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:50:44.223231+00:00
-- url     : https://prove2.me/submissions/b779612a-c468-46e4-838c-b339e0ee5536

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_WeightAddLeOfMemSupportDividedContraction

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
theorem _root_.solution (γ : ι → κ → R) (P : MvPolynomial (ι ⊕ κ) R) :
    contraction γ P = ∑ i, ∑ j, γ i j • pderiv (Sum.inl i) (pderiv (Sum.inr j) P) := by
  simp [contraction, LinearMap.sum_apply]
end GlobalTheory.Wick
