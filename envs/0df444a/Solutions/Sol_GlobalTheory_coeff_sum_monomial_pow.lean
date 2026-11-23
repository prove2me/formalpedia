-- Prove2me | solution 1 for GlobalTheory.coeff_sum_monomial_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:49:43.71119+00:00
-- url     : https://prove2.me/submissions/3ea49abd-195b-4d5b-b94d-ab3a26412c42

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CardRootsClosedBallBoundsUltrametricStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AdditivePolyTaylorCoeffSubNormLeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FewRootsSmallDisc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open Classical
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (l : ℕ) [Fact l.Prime] (E : ℕ) (a : ℕ → ℂ_[l]) (k : ℕ)
    (hk : k ≤ E) :
    (∑ i ∈ Finset.range (E + 1), monomial (l ^ i) (a i) : ℂ_[l][X]).coeff (l ^ k) = a k := by
  have hl : 2 ≤ l := (Fact.out : l.Prime).two_le
  rw [finsetSum_coeff, Finset.sum_eq_single k]
  · simp [coeff_monomial]
  · intro i _ hik
    rw [coeff_monomial, if_neg]
    intro h
    exact hik (Nat.pow_right_injective hl h)
  · intro h
    exact absurd (Finset.mem_range.mpr (by omega)) h
end GlobalTheory
