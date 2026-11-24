-- Prove2me | solution 1 for GlobalTheory.T.lie_algebra_of_tangent_curve
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:17:08.497301+00:00
-- url     : https://prove2.me/submissions/eccac602-bfde-45d1-bc85-fea47d0d3d52

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LieAlgebraOfTangentCurve
import Definitions.Def_Formalism_UnipotentAdelicQuotients_SmComplete
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LieAlgebraOfTangentCurveStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_SmTangent_tangent_mem_lieAlg


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open SmoothVectors Filter Topology
open scoped ContDiff Matrix.Norms.Elementwise
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (n : ℕ) (G : Set (Matrix (Fin n) (Fin n) ℂ)), IsClosedMatrixGroup G → ∀ (γ : ℝ → Matrix (Fin n) (Fin n) ℂ) (Y : Matrix (Fin n) (Fin n) ℂ), γ 0 = 1 → (∀ᶠ t in 𝓝 (0 : ℝ), γ t ∈ G) → HasDerivAt γ Y 0 → Y ∈ lieAlg G := by
  first | exact @GlobalTheory.CompanionTheory.SmTangent.tangent_mem_lieAlg | exact GlobalTheory.CompanionTheory.SmTangent.tangent_mem_lieAlg | (intros; apply GlobalTheory.CompanionTheory.SmTangent.tangent_mem_lieAlg <;> assumption)
end _root_.GlobalTheory.T
