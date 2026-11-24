-- Prove2me | solution 1 for GlobalTheory.Ker.CreOp.contDiff_fderiv_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:29:48.78203+00:00
-- url     : https://prove2.me/submissions/934dc4e1-b6c0-496f-a908-a84b86d59490

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_FoldrHolDEqIteratedFDeriv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex
open scoped ComplexConjugate
open GlobalTheory GlobalTheory.Ker GlobalTheory.Ker.CreOp
variable {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W]
namespace GlobalTheory.Ker.CreOp
theorem _root_.solution {Φ : W → ℂ} (h : ContDiff ℝ (⊤ : ℕ∞) Φ) (v : W) :
    ContDiff ℝ (⊤ : ℕ∞) fun z => fderiv ℝ Φ z v := (contDiff_infty_iff_fderiv.1 h).2.clm_apply contDiff_const
end GlobalTheory.Ker.CreOp
