-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SmoothParam.hasFDerivAt_partial
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:07:00.917098+00:00
-- url     : https://prove2.me/submissions/ec3a653d-447e-4143-a91d-2f636a6e1a8b

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ContDiffIntegralDensity

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
theorem _root_.solution {H : P × Y → F} (hH : Differentiable ℝ H) (p : P) (y : Y) :
    HasFDerivAt (fun q => H (q, y))
      ((fderiv ℝ H (p, y)).comp (ContinuousLinearMap.inl ℝ P Y)) p :=
  (hH (p, y)).hasFDerivAt.comp p (hasFDerivAt_prodMk_left p y)
end GlobalTheory.CompanionTheory.SmoothParam
