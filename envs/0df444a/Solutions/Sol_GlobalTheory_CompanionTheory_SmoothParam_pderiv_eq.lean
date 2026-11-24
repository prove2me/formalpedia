-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SmoothParam.pderiv_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:40:26.828771+00:00
-- url     : https://prove2.me/submissions/21a3efb5-bd96-4343-b125-6fac1408334a

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ContDiffIntegralDensity
import Theorems.Thm_GlobalTheory_CompanionTheory_SmoothParam_hasFDerivAt_partial

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
theorem _root_.solution {H : P × Y → F} (hH : Differentiable ℝ H) :
    pderiv H = fun z => (fderiv ℝ H z).comp (ContinuousLinearMap.inl ℝ P Y) := by
  funext z
  exact (hasFDerivAt_partial hH z.1 z.2).fderiv
end GlobalTheory.CompanionTheory.SmoothParam
