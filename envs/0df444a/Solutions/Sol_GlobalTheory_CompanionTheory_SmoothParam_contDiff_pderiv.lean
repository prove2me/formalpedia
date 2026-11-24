-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SmoothParam.contDiff_pderiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T14:01:32.167501+00:00
-- url     : https://prove2.me/submissions/603a8d5b-662f-4035-9339-88324fc97e50

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ContDiffIntegralDensity
import Theorems.Thm_GlobalTheory_CompanionTheory_SmoothParam_pderiv_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology
open scoped ContDiff
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SmoothParam
variable {Ω P Y F : Type} [MeasurableSpace Ω] [NormedAddCommGroup P] [NormedSpace ℝ P]
  [FiniteDimensional ℝ P] [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
omit [FiniteDimensional ℝ P] [FiniteDimensional ℝ Y]
namespace GlobalTheory.CompanionTheory.SmoothParam
theorem _root_.solution {H : P × Y → F} (hH : ContDiff ℝ ∞ H) : ContDiff ℝ ∞ (pderiv H) := by
  rw [pderiv_eq (hH.differentiable (by simp))]
  have h1 : ContDiff ℝ ∞ (fderiv ℝ H) := hH.fderiv_right (by simp)
  exact h1.clm_comp contDiff_const
end GlobalTheory.CompanionTheory.SmoothParam
