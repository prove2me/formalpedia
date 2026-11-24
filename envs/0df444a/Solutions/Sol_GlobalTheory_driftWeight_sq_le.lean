-- Prove2me | solution 1 for GlobalTheory.driftWeight_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:36:08.155504+00:00
-- url     : https://prove2.me/submissions/018941f8-5f6e-46c5-8649-d44bb630a015

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_WeightedSumDriftInequality

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology Matrix
open scoped ComplexOrder ENNReal Pointwise
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (ε : ℝ) (h0 : 0 ≤ ε) (h1 : ε ≤ 1) (r i j : ℕ) (hj : 0 < j) (hji : j ≤ i)
    (hr : i + j ≤ r) :
    (ε ^ (i * (r - i))) ^ 2 ≤
      ε ^ 2 * (ε ^ ((i - j) * (r - (i - j))) * ε ^ ((i + j) * (r - (i + j)))) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hji
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hr
  have e1 : j + m + j + k - (j + m) = j + k := by omega
  have e2 : j + m - j = m := by omega
  have e3 : j + m + j + k - m = j + j + k := by omega
  have e4 : j + m + j + k - (j + m + j) = k := by omega
  rw [e1, e2, e3, e4, ← pow_add, ← pow_add, ← pow_mul]
  apply pow_le_pow_of_le_one h0 h1
  nlinarith [Nat.mul_le_mul hj hj]
end GlobalTheory
