-- Prove2me | solution 1 for GlobalTheory.Ker.CreOp.holD_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:29:50.29288+00:00
-- url     : https://prove2.me/submissions/7848290f-92d9-4263-a3af-6394bd394d1a

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
theorem _root_.solution {Φ Ψ : W → ℂ} (h : Differentiable ℝ Φ) (h' : Differentiable ℝ Ψ) (v : W) :
    holD v (fun z => Φ z + Ψ z) = fun z => holD v Φ z + holD v Ψ z := by
  funext z
  have hs : HasFDerivAt (fun y => Φ y + Ψ y) (fderiv ℝ Φ z + fderiv ℝ Ψ z) z :=
    (h z).hasFDerivAt.add (h' z).hasFDerivAt
  simp only [holD, hs.fderiv, ContinuousLinearMap.add_apply]
  ring
end GlobalTheory.Ker.CreOp
