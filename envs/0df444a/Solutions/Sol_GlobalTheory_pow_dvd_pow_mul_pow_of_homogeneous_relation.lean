-- Prove2me | solution 1 for GlobalTheory.pow_dvd_pow_mul_pow_of_homogeneous_relation
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:29:49.763844+00:00
-- url     : https://prove2.me/submissions/ffa2c147-a00e-465c-bc26-03845b2b38c5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsValuationSubringAlgClosedNotIsUnitStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_BoundedPowersOrExistsValuationSubringDvd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped NNReal
open Polynomial
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {R : Type*} [CommRing R] (v x : R)
    (q : ℕ → R) (n N : ℕ) (h0 : IsUnit (q 0))
    (h : x ^ N * ∑ i ∈ Finset.range (n + 1), q i * v ^ i * x ^ (n - i) = 0) (j : ℕ) :
    v ^ j ∣ v ^ (N + n) * x ^ j := by
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    by_cases hj : j ≤ N + n
    · exact Dvd.dvd.mul_right (pow_dvd_pow v hj) _
    · obtain ⟨d, rfl⟩ : ∃ d, j = N + n + d := ⟨j - (N + n), by omega⟩
      rw [Finset.sum_range_succ'] at h
      have key : q 0 * (v ^ (N + n) * x ^ (N + n + d)) =
          - ∑ i ∈ Finset.range n,
            v ^ (N + n) * x ^ d * x ^ N * (q (i + 1) * v ^ (i + 1) * x ^ (n - (i + 1))) := by
        rw [← Finset.mul_sum]
        simp only [pow_zero, mul_one, Nat.sub_zero] at h
        linear_combination (v ^ (N + n) * x ^ d) * h
      rw [← h0.dvd_mul_left, key, dvd_neg]
      refine Finset.dvd_sum fun i hi => ?_
      have hi' : i < n := Finset.mem_range.1 hi
      obtain ⟨e, rfl⟩ : ∃ e, n = i + 1 + e := ⟨n - (i + 1), by omega⟩
      obtain ⟨w, hw⟩ := ih (N + e + d) (by omega)
      refine ⟨q (i + 1) * w, ?_⟩
      rw [Nat.add_sub_cancel_left]
      linear_combination (q (i + 1) * v ^ (i + 1)) * hw
end GlobalTheory
