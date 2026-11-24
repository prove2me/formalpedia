-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Kloc.Fresnel.kerOp_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:40:56.28881+00:00
-- url     : https://prove2.me/submissions/618c8997-e970-4f6a-a298-5bc8c84f4939

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
theorem _root_.solution (C : ℂ) (a : ℝ) (R : V ≃ₗᵢ[ℝ] V) (g : V → ℂ) :
    kerOp C a R g 0 = C * ∫ v, g v := by
  simp [kerOp]
end GlobalTheory.CompanionTheory.Kloc.Fresnel
