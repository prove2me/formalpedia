-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Kloc.Fresnel.norm_cexp_le_one_of_re_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:48:21.816096+00:00
-- url     : https://prove2.me/submissions/483592c8-599f-4499-bb9d-978d39124daa

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FourierTransformMatrixSpaceInvolution

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Complex
open scoped FourierTransform RealInnerProductSpace SchwartzMap Matrix
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Kloc GlobalTheory.CompanionTheory.Kloc.Fresnel
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
namespace GlobalTheory.CompanionTheory.Kloc.Fresnel
theorem _root_.solution {z : ℂ} (h : z.re ≤ 0) : ‖cexp z‖ ≤ 1 := by
  rw [Complex.norm_exp]; exact Real.exp_le_one_iff.2 h
end GlobalTheory.CompanionTheory.Kloc.Fresnel
