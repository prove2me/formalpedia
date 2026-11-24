-- Prove2me | solution 1 for GlobalTheory.T.weakSolution_of_smooth_solution
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:41:19.287846+00:00
-- url     : https://prove2.me/submissions/fac0b204-04cb-4fe7-8fe8-133abd080126

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_WeakSolutionOfSmoothSolution
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ZeroMemSolSet
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllRegCheck
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_WeakSolutionOfSmoothSolutionStatement
import Theorems.Thm_GlobalTheory_HCA_weakSol_of_smooth


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ZetaZeros.D.EllReg GlobalTheory.HCA MeasureTheory
open scoped ContDiff BoundedContinuousFunction
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (d m : ℕ) (U : Set (E d)), IsOpen U → ∀ (a : (n : ℕ) → (Fin n → Fin d) → E d → ℂ), (∀ n w, ContDiffOn ℝ ∞ (a n w) U) → ∀ u : E d → ℂ, ContDiffOn ℝ ∞ u U → (∀ x ∈ U, apOp m a u x = 0) → WeakSol (oneSys m a) U u := by
  first | exact @GlobalTheory.HCA.weakSol_of_smooth | exact GlobalTheory.HCA.weakSol_of_smooth | (intros; apply GlobalTheory.HCA.weakSol_of_smooth <;> assumption)
end _root_.GlobalTheory.T
