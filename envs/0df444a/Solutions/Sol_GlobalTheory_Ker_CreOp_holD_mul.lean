-- Prove2me | solution 1 for GlobalTheory.Ker.CreOp.holD_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:29:51.055616+00:00
-- url     : https://prove2.me/submissions/4eb4d705-08d8-40f1-990a-55c29630001b

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
theorem _root_.solution (T : W →L[ℝ] ℂ) (h2 : ∀ a, T (I • a) = -I * T a) {Φ : W → ℂ}
    (h : Differentiable ℝ Φ) (v : W) :
    holD v (fun z => T z * Φ z) = fun z => T z * holD v Φ z := by
  funext z
  have hT : HasFDerivAt (fun y => T y * Φ y) (T z • fderiv ℝ Φ z + Φ z • T) z :=
    T.hasFDerivAt.mul (h z).hasFDerivAt
  simp only [holD, hT.fderiv, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul, h2]
  linear_combination (1 / 2 : ℂ) * Φ z * T v * I_sq
end GlobalTheory.Ker.CreOp
