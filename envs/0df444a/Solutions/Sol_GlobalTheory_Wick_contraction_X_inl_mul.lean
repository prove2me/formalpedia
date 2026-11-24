-- Prove2me | solution 1 for GlobalTheory.Wick.contraction_X_inl_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:17:47.53782+00:00
-- url     : https://prove2.me/submissions/410d69fc-d535-4fce-9669-cf0b0767d3f4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_WeightAddLeOfMemSupportDividedContraction
import Theorems.Thm_GlobalTheory_Wick_contraction_eq_sum

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
theorem _root_.solution (γ : ι → κ → R) (i : ι) (P : MvPolynomial (ι ⊕ κ) R) :
    contraction γ (X (Sum.inl i) * P) = X (Sum.inl i) * contraction γ P + rowContraction γ i P := by
  classical
  simp [contraction_eq_sum, LinearMap.sum_apply, rowContraction_X_inl_mul, Finset.mul_sum,
    pderiv_X, Finset.sum_add_distrib, Pi.single_apply]
end GlobalTheory.Wick
