-- Prove2me | solution 1 for GlobalTheory.WittIntegrality.teich_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:17:58.604652+00:00
-- url     : https://prove2.me/submissions/4d67d1ac-0e23-4906-88c3-c0220621801a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WittMatrixCoeffMemOfFrobenius
import Theorems.Thm_GlobalTheory_WittIntegrality_mem_S

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
namespace GlobalTheory.WittIntegrality
theorem _root_.solution {c : C} (hc : c ∈ A) : teichmuller p c ∈ S A p := by
  rw [mem_S]
  intro k
  cases k with
  | zero => rwa [teichmuller_coeff_zero]
  | succ k => rw [teichmuller_coeff_pos p c _ (Nat.succ_pos k)]; exact A.zero_mem
end GlobalTheory.WittIntegrality
