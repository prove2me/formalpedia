-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Kloc.Fresnel.matEquiv_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:51:04.055383+00:00
-- url     : https://prove2.me/submissions/96b4de1a-ebdd-41b3-b6d0-43ba8db6250f

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
theorem _root_.solution (u : Fin m → Fin n → ℂ) (p : Fin m × Fin n) :
    matEquiv m n u p = u p.1 p.2 := rfl
end GlobalTheory.CompanionTheory.Kloc.Fresnel
