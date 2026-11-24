-- Prove2me | solution 1 for GlobalTheory.T.polynomial_times_gaussian_bounded
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:21:19.59796+00:00
-- url     : https://prove2.me/submissions/ee01e432-fe23-4de4-a100-a656e30c00d7

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_PolynomialTimesGaussianBounded
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_PolynomialTimesGaussianBoundedStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_EisTube_polyGaussBdd


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (ι : Type) [Fintype ι] (c : ℝ), 0 < c → ∀ N : ℕ, ∃ M : ℝ, ∀ y : ι → ℝ,
    (1 + ‖y‖) ^ N * Real.exp (-(c * ∑ i, y i ^ 2)) ≤ M := by
  first | exact @GlobalTheory.CompanionTheory.EisTube.polyGaussBdd | exact GlobalTheory.CompanionTheory.EisTube.polyGaussBdd | (intros; apply GlobalTheory.CompanionTheory.EisTube.polyGaussBdd <;> assumption)
end _root_.GlobalTheory.T
