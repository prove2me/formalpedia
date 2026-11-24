-- Prove2me | solution 1 for GlobalTheory.WrongSignGauss.twD_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:42:43.252465+00:00
-- url     : https://prove2.me/submissions/8869c31b-a00c-40ff-9637-c21a433cbe35

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
theorem _root_.solution (a : V) (ℓ : V →ₗ[ℝ] ℝ) (f : 𝓢(V, ℂ)) (x : V) :
    twD a ℓ f x = ∂_{a} f x - 2 * Real.pi * Complex.I * ((ℓ x : ℂ) * f x) := by
  simp [twD, mulForm_apply]
end GlobalTheory.WrongSignGauss
