-- Prove2me | solution 1 for GlobalTheory.Ker.CreOp.contDiff_holD
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:45:11.273151+00:00
-- url     : https://prove2.me/submissions/81af15ba-5934-4741-af38-5f7dbbc37a16

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_FoldrHolDEqIteratedFDeriv
import Theorems.Thm_GlobalTheory_Ker_CreOp_contDiff_fderiv_apply

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
    ContDiff ℝ (⊤ : ℕ∞) (holD v Φ) := by
  show ContDiff ℝ _ fun z => (1 / 2 : ℂ) * (fderiv ℝ Φ z v - I * fderiv ℝ Φ z (I • v))
  exact contDiff_const.mul
    ((contDiff_fderiv_apply h v).sub (contDiff_const.mul (contDiff_fderiv_apply h (I • v))))
end GlobalTheory.Ker.CreOp
