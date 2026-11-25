-- Prove2me | solution 1 for GlobalTheory.T.lattice_epstein_zeta_continuation
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:49:09.38145+00:00
-- url     : https://prove2.me/submissions/bede6d49-3f85-4282-906e-b484e81722e9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_LatticeEpsteinZetaContinuation
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_NonemptyRayDataOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_LatticeEpsteinZetaContinuationStatement
import Theorems.Thm_GlobalTheory_epsteinZeta_shifted_continuation


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Asymptotics
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (w₁ w₂ x₀ : ℂ), (starRingEnd ℂ w₁ * w₂).im ≠ 0 → (∀ m n : ℤ, x₀ + m * w₁ + n * w₂ ≠ 0) → ∃ Z : ℂ → ℂ, Differentiable ℂ Z ∧ Z 1 = (Real.pi / |(starRingEnd ℂ w₁ * w₂).im| : ℝ) ∧ Z (-1) = 0 ∧ ∀ s : ℂ, 1 < s.re → Summable (fun p : ℤ × ℤ => ((‖x₀ + p.1 * w₁ + p.2 * w₂‖ ^ 2 : ℝ) : ℂ) ^ (-s)) ∧ Z s = (s - 1) * ∑' p : ℤ × ℤ, ((‖x₀ + p.1 * w₁ + p.2 * w₂‖ ^ 2 : ℝ) : ℂ) ^ (-s) := by
  first | exact @GlobalTheory.epsteinZeta_shifted_continuation | exact GlobalTheory.epsteinZeta_shifted_continuation | (intros; apply GlobalTheory.epsteinZeta_shifted_continuation <;> assumption)
end _root_.GlobalTheory.T
