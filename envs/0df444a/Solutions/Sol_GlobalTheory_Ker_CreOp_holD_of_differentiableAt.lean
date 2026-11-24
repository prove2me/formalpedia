-- Prove2me | solution 1 for GlobalTheory.Ker.CreOp.holD_of_differentiableAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:29:51.732268+00:00
-- url     : https://prove2.me/submissions/0cb084aa-4ace-47a9-91ca-a4ccae0227ab

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
theorem _root_.solution {Φ : W → ℂ} {z : W} (h : DifferentiableAt ℂ Φ z) (v : W) :
    holD v Φ z = fderiv ℂ Φ z v := by
  have e : fderiv ℝ Φ z = (fderiv ℂ Φ z).restrictScalars ℝ := h.fderiv_restrictScalars ℝ
  simp only [holD, e, ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.map_smul,
    smul_eq_mul]
  linear_combination (-(1 / 2) : ℂ) * fderiv ℂ Φ z v * I_sq
end GlobalTheory.Ker.CreOp
