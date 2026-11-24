-- Prove2me | solution 1 for GlobalTheory.T.lie_algebra_function_calculus
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:17:07.45531+00:00
-- url     : https://prove2.me/submissions/a845b467-6d76-4502-80cf-654a48c41865

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LieAlgebraFunctionCalculus
import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LieAlgebraFunctionCalculusStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_AdProj_mem_of_entrywise


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Topology Filter
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {n : ℕ} (𝔤 : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) (h : Fin n → ℝ), Matrix.diagonal (fun i => (h i : ℂ)) ∈ 𝔤 → (∀ X ∈ 𝔤, ∀ Y ∈ 𝔤, X * Y - Y * X ∈ 𝔤) → ∀ (f : ℝ → ℝ), ∀ X ∈ 𝔤, (Matrix.of fun i j => (f (h i - h j) : ℂ) * X i j) ∈ 𝔤 := by
  first | exact @GlobalTheory.CompanionTheory.AdProj.mem_of_entrywise | exact GlobalTheory.CompanionTheory.AdProj.mem_of_entrywise | (intros; apply GlobalTheory.CompanionTheory.AdProj.mem_of_entrywise <;> assumption)
end _root_.GlobalTheory.T
