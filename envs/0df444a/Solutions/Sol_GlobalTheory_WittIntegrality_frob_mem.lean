-- Prove2me | solution 1 for GlobalTheory.WittIntegrality.frob_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:17:56.377645+00:00
-- url     : https://prove2.me/submissions/6fab0573-5433-4316-a013-e8dd6658dbd7

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
variable [CharP C p]
namespace GlobalTheory.WittIntegrality
theorem _root_.solution {x : WittVector p C} (hx : x ∈ S A p) : frobenius x ∈ S A p := by
  rw [mem_S] at hx ⊢
  intro k
  rw [coeff_frobenius_charP]
  exact pow_mem (hx k) _
end GlobalTheory.WittIntegrality
