-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.EisTube.inner_eq_sum_coord
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:26:26.601035+00:00
-- url     : https://prove2.me/submissions/5d2cec85-95e4-4929-88f5-d644b2dadb3b

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FourierInversionFiniteDim

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped FourierTransform RealInnerProductSpace
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.EisTube
universe u
namespace GlobalTheory.CompanionTheory.EisTube
theorem _root_.solution {ι : Type} [Fintype ι] (v w : EuclideanSpace ℝ ι) :
    ⟪v, w⟫ = ∑ i, v i * w i := by
  simp [PiLp.inner_apply, mul_comm]
end GlobalTheory.CompanionTheory.EisTube
