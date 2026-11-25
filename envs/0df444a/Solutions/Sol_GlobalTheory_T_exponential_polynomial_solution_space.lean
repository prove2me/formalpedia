-- Prove2me | solution 1 for GlobalTheory.T.exponential_polynomial_solution_space
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:21:43.702564+00:00
-- url     : https://prove2.me/submissions/a9520671-f474-4638-8942-2a0d139f11d7

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExponentialPolynomialSolutionSpace
import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExponentialPolynomialSolutionSpaceStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_ConstCoeffODE_solutions_mem_finite


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ l : List ℂ, ∃ S : Submodule ℂ (ℝ → ℂ), FiniteDimensional ℂ S ∧ Module.finrank ℂ S ≤ l.length ∧
  ∀ (X : Type) [AddCommGroup X] [Module ℂ X] (D : Module.End ℂ X) (ev : X →ₗ[ℂ] (ℝ → ℂ)),
    (∀ x t, HasDerivAt (ev x) (ev (D x) t) t) → ∀ x, ev ((l.map fun c => D - c • (1 : Module.End ℂ X)).prod x) = 0 → ev x ∈ S := by
  first | exact @GlobalTheory.CompanionTheory.ConstCoeffODE.solutions_mem_finite | exact GlobalTheory.CompanionTheory.ConstCoeffODE.solutions_mem_finite | (intros; apply GlobalTheory.CompanionTheory.ConstCoeffODE.solutions_mem_finite <;> assumption)
end _root_.GlobalTheory.T
