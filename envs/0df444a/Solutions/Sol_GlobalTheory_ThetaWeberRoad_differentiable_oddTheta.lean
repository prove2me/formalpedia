-- Prove2me | solution 1 for GlobalTheory.ThetaWeberRoad.differentiable_oddTheta
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:29:13.672281+00:00
-- url     : https://prove2.me/submissions/e7fb5e68-5a04-427d-b1a7-e5cd3a2b22bb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_GlobalSignature_ThetaConstantWeber
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_DifferentiableOddTheta

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex
open UpperHalfPlane hiding I
open scoped Real
noncomputable section
open GlobalTheory GlobalTheory.ThetaWeberRoad
namespace GlobalTheory.ThetaWeberRoad
theorem _root_.solution (τ : ℍ) : Differentiable ℂ (oddTheta τ) := by
  intro z
  have hexp : DifferentiableAt ℂ
      (fun w : ℂ => cexp (π * I * (τ : ℂ) / 4 + π * I * (w + 1 / 2))) z := by
    fun_prop
  have hshift : DifferentiableAt ℂ (fun w : ℂ => w + ((τ : ℂ) + 1) / 2) z :=
    differentiableAt_id.add_const _
  have htheta : DifferentiableAt ℂ
      (fun w : ℂ => jacobiTheta₂ (w + ((τ : ℂ) + 1) / 2) τ) z := by
    have h0 : DifferentiableAt ℂ (fun w : ℂ => jacobiTheta₂ w τ) (z + ((τ : ℂ) + 1) / 2) :=
      differentiableAt_jacobiTheta₂_fst _ τ.2
    exact h0.comp z hshift
  exact hexp.mul htheta
end GlobalTheory.ThetaWeberRoad
