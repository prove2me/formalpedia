-- Prove2me | solution 1 for GlobalTheory.ArtinKernel.differentiable_fderiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:27:39.65162+00:00
-- url     : https://prove2.me/submissions/0435a442-6304-42bd-9ef0-e58b2d109c3d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EntireApplyEqOfPeriodicOfSpanReal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsLinearOfMulPeriod
import Theorems.Thm_GlobalTheory_SCV_differentiableOn_fderiv


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Topology
open GlobalTheory GlobalTheory.ArtinKernel
namespace GlobalTheory.ArtinKernel
theorem _root_.solution {g : ℕ} {F : (Fin g → ℂ) → ℂ} (hF : Differentiable ℂ F) :
    Differentiable ℂ (fderiv ℂ F) := differentiableOn_univ.mp (GlobalTheory.SCV.differentiableOn_fderiv isOpen_univ hF.differentiableOn)
end GlobalTheory.ArtinKernel
