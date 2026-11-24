-- Prove2me | solution 1 for GlobalTheory.Wick.commute_contraction_rowContraction
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:17:46.71205+00:00
-- url     : https://prove2.me/submissions/0eab38be-7586-45d6-873f-dfe5e810acc3

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
theorem _root_.solution (γ : ι → κ → R) (i : ι) :
    Commute (contraction γ) (rowContraction γ i) := by
  rw [contraction_eq_sum]
  exact Commute.sum_left _ _ _ fun i' _ =>
    (commute_pderiv_rowContraction _ _ _).mul_left (commute_rowContraction _ _ _)
end GlobalTheory.Wick
