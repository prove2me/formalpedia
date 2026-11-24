-- Prove2me | solution 1 for GlobalTheory.Ker.CreOp.contDiff_foldr_holD
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:00:41.182278+00:00
-- url     : https://prove2.me/submissions/8b316dfb-1771-4236-9887-2c3e485f7708

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_FoldrHolDEqIteratedFDeriv
import Theorems.Thm_GlobalTheory_Ker_CreOp_contDiff_holD

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
variable {σ : Type} (u : σ → W)
namespace GlobalTheory.Ker.CreOp
theorem _root_.solution {Φ : W → ℂ} (h : ContDiff ℝ (⊤ : ℕ∞) Φ) (M : List σ) :
    ContDiff ℝ (⊤ : ℕ∞) (M.foldr (fun l => holD (u l)) Φ) := by
  induction M with
  | nil => exact h
  | cons l M ih => exact contDiff_holD ih (u l)
end GlobalTheory.Ker.CreOp
