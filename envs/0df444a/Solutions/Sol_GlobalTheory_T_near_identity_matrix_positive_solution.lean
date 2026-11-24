-- Prove2me | solution 1 for GlobalTheory.T.near_identity_matrix_positive_solution
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:19:35.272328+00:00
-- url     : https://prove2.me/submissions/5e7944e1-3193-4558-bad0-3d44aa84533f

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_NearIdentityMatrixPositiveSolution
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_NearIdentityMatrixPositiveSolutionStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_DiagDom_small_perturbation_injective_pos


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {κ : Type} [Fintype κ] [DecidableEq κ] (M : ℝ), ∃ ε : ℝ, 0 < ε ∧ ∀ W : κ → κ → ℝ, (∀ σ i, |W σ i - if σ = i then 1 else 0| < ε) →
    (∀ c : κ → ℝ, (∀ σ, ∑ i, W σ i * c i = 0) → c = 0) ∧
    ∀ c : κ → ℝ, (∀ σ, 0 < ∑ i, W σ i * c i) → (∀ σ τ, ∑ i, W σ i * c i ≤ M * ∑ i, W τ i * c i) → ∀ i, 0 < c i := by
  first | exact @GlobalTheory.CompanionTheory.DiagDom.small_perturbation_injective_pos | exact GlobalTheory.CompanionTheory.DiagDom.small_perturbation_injective_pos | (intros; apply GlobalTheory.CompanionTheory.DiagDom.small_perturbation_injective_pos <;> assumption)
end _root_.GlobalTheory.T
