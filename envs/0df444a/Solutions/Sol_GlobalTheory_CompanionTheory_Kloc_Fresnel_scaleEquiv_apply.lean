-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Kloc.Fresnel.scaleEquiv_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:10:25.317804+00:00
-- url     : https://prove2.me/submissions/f9ae5226-8454-4ff3-ac85-0dbc323dd4ed

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
theorem _root_.solution (a : ℝ) (ha : a ≠ 0) (R : V ≃ₗᵢ[ℝ] V) (u : V) :
    scaleEquiv a ha R u = (-a) • R.symm u := rfl
end GlobalTheory.CompanionTheory.Kloc.Fresnel
