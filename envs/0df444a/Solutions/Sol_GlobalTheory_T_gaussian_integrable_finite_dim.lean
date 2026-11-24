-- Prove2me | solution 1 for GlobalTheory.T.gaussian_integrable_finite_dim
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:10:57.069015+00:00
-- url     : https://prove2.me/submissions/e66e4420-0da9-47be-8585-bfdd1e0622b8

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GaussianIntegrableFiniteDim
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GaussianIntegrableFiniteDimStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_EisTube_gaussInt


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
theorem _root_.solution : ∀ (ι : Type) [Fintype ι] (c : ℝ), 0 < c →
    MeasureTheory.Integrable (fun y : ι → ℝ => Real.exp (-(c * ∑ i, y i ^ 2))) := by
  first | exact @GlobalTheory.CompanionTheory.EisTube.gaussInt | exact GlobalTheory.CompanionTheory.EisTube.gaussInt | (intros; apply GlobalTheory.CompanionTheory.EisTube.gaussInt <;> assumption)
end _root_.GlobalTheory.T
