-- Prove2me | solution 1 for GlobalTheory.WittIntegrality.decomp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:17:55.495463+00:00
-- url     : https://prove2.me/submissions/67e2814b-8b09-47da-9367-2b10060b7bdc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WittMatrixCoeffMemOfFrobenius
import Theorems.Thm_GlobalTheory_WittIntegrality_tail_coeff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped PowerSeries Pointwise
open GlobalTheory
open GlobalTheory.WittIntegrality
open WittVector
variable {C : Type} [Field C] (A : ValuationSubring C)
variable (p : ℕ) [hp : Fact p.Prime]
variable {p}
variable [CharP C p]
variable [PerfectRing C p]
namespace GlobalTheory.WittIntegrality
theorem _root_.solution (x : WittVector p C) : x = teichmuller p (x.coeff 0) + tail x * p := by
  ext k
  rw [coeff_add_of_disjoint]
  · cases k with
    | zero => rw [teichmuller_coeff_zero, mul_charP_coeff_zero, add_zero]
    | succ k =>
      rw [teichmuller_coeff_pos p _ _ (Nat.succ_pos k), mul_charP_coeff_succ, zero_add, tail_coeff]
  · intro k
    cases k with
    | zero => exact Or.inr (mul_charP_coeff_zero _)
    | succ k => exact Or.inl (teichmuller_coeff_pos p _ _ (Nat.succ_pos k))
end GlobalTheory.WittIntegrality
