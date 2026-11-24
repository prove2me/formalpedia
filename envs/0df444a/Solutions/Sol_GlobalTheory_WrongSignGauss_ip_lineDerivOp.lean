-- Prove2me | solution 1 for GlobalTheory.WrongSignGauss.ip_lineDerivOp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:17:52.104838+00:00
-- url     : https://prove2.me/submissions/ef6e6348-fb63-49df-a765-9ec338ea673a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SchwartzEqZeroOfWrongSignGaussianRelation
import Theorems.Thm_GlobalTheory_WrongSignGauss_sesq_apply
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
theorem _root_.solution (a : V) (u w : 𝓢(V, ℂ)) : ip μ (∂_{a} u) w = - ip μ u (∂_{a} w) := by
  have h := integral_bilinear_lineDerivOp_right_eq_neg_left (μ := μ) u w sesq a
  simp only [sesq_apply] at h
  simp only [ip, h, neg_neg]
end GlobalTheory.WrongSignGauss
