-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Kloc.Fresnel.unitMul_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:42:12.070215+00:00
-- url     : https://prove2.me/submissions/2b8f8c77-e553-47eb-9d97-f5d56a9b6968

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
variable {m n : ℕ}
namespace GlobalTheory.CompanionTheory.Kloc.Fresnel
theorem _root_.solution (ι : Type) [Fintype ι] (ω : ℂ) (hω : ‖ω‖ = 1) (x : EuclideanSpace ℂ ι) :
    unitMul ι ω hω x = ω • x := rfl
end GlobalTheory.CompanionTheory.Kloc.Fresnel
