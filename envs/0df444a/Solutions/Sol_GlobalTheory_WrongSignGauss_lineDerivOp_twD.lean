-- Prove2me | solution 1 for GlobalTheory.WrongSignGauss.lineDerivOp_twD
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:28:07.149993+00:00
-- url     : https://prove2.me/submissions/c3eadb8b-e6e7-47bb-ba67-fb966a042091

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SchwartzEqZeroOfWrongSignGaussianRelation
import Theorems.Thm_GlobalTheory_WrongSignGauss_sesq_apply
import Theorems.Thm_GlobalTheory_WrongSignGauss_lineDerivOp_mulForm
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
theorem _root_.solution (v a : V) (ℓ : V →ₗ[ℝ] ℝ) (f : 𝓢(V, ℂ)) (x : V) :
    ∂_{v} (twD a ℓ f) x = ∂_{v} (∂_{a} f) x -
      2 * Real.pi * Complex.I * ((ℓ x : ℂ) * ∂_{v} f x + (ℓ v : ℂ) * f x) := by
  rw [twD, ← LineDeriv.lineDerivOpCLM_apply (R := ℂ), map_sub, map_smul,
    LineDeriv.lineDerivOpCLM_apply, LineDeriv.lineDerivOpCLM_apply]
  simp only [SchwartzMap.sub_apply, SchwartzMap.smul_apply, smul_eq_mul, lineDerivOp_mulForm]
end GlobalTheory.WrongSignGauss
