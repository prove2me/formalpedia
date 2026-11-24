-- Prove2me | solution 1 for GlobalTheory.WrongSignGauss.ip_twD
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:28:06.415015+00:00
-- url     : https://prove2.me/submissions/da411cb5-c1b3-4b4a-b236-2f5152764057

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SchwartzEqZeroOfWrongSignGaussianRelation
import Theorems.Thm_GlobalTheory_WrongSignGauss_sesq_apply
import Theorems.Thm_GlobalTheory_WrongSignGauss_ip_smul_left
import Theorems.Thm_GlobalTheory_WrongSignGauss_ip_smul_right
import Theorems.Thm_GlobalTheory_WrongSignGauss_ip_sub_left
import Theorems.Thm_GlobalTheory_WrongSignGauss_ip_sub_right
import Theorems.Thm_GlobalTheory_WrongSignGauss_ip_lineDerivOp
import Theorems.Thm_GlobalTheory_WrongSignGauss_ip_mulForm
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
variable [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure]
namespace GlobalTheory.WrongSignGauss
theorem _root_.solution (a : V) (ℓ : V →ₗ[ℝ] ℝ) (u w : 𝓢(V, ℂ)) :
    ip μ (twD a ℓ u) w = - ip μ u (twD a ℓ w) := by
  simp only [twD, ip_sub_left, ip_sub_right, ip_smul_left, ip_smul_right, ip_lineDerivOp, ip_mulForm]
  simp [map_mul, Complex.conj_ofReal, map_ofNat]
  ring
end GlobalTheory.WrongSignGauss
