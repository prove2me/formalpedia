-- Prove2me | solution 1 for GlobalTheory.WrongSignGauss.lineDerivOp_mulForm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:17:57.72483+00:00
-- url     : https://prove2.me/submissions/78515564-2757-4e7f-a27b-f44904a57b41

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SchwartzEqZeroOfWrongSignGaussianRelation
import Theorems.Thm_GlobalTheory_WrongSignGauss_sesq_apply
import Theorems.Thm_GlobalTheory_WrongSignGauss_mulForm_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.WrongSignGauss.sesq_apply

set_option autoImplicit false
open SchwartzMap LineDeriv MeasureTheory ComplexConjugate
noncomputable section
open GlobalTheory GlobalTheory.WrongSignGauss
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
namespace GlobalTheory.WrongSignGauss
theorem _root_.solution (v : V) (ℓ : V →ₗ[ℝ] ℝ) (f : 𝓢(V, ℂ)) (x : V) :
    ∂_{v} (mulForm ℓ f) x = (ℓ x : ℂ) * ∂_{v} f x + (ℓ v : ℂ) * f x := by
  have e : (⇑(mulForm ℓ f)) = ⇑(LinearMap.toContinuousLinearMap ℓ) • ⇑f := by
    funext y; rw [Pi.smul_apply', mulForm_apply, Complex.real_smul]; rfl
  have h2 := ((LinearMap.toContinuousLinearMap ℓ).hasFDerivAt (x := x)).smul (f.hasFDerivAt x)
  rw [SchwartzMap.lineDerivOp_apply_eq_fderiv, e, h2.fderiv]
  simp [SchwartzMap.lineDerivOp_apply_eq_fderiv, Complex.real_smul]
end GlobalTheory.WrongSignGauss
