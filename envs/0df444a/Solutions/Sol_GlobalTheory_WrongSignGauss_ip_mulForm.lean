-- Prove2me | solution 1 for GlobalTheory.WrongSignGauss.ip_mulForm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:17:52.853135+00:00
-- url     : https://prove2.me/submissions/d2150b75-c745-4315-9e5e-227e98759890

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
variable [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure]
namespace GlobalTheory.WrongSignGauss
theorem _root_.solution (ℓ : V →ₗ[ℝ] ℝ) (u w : 𝓢(V, ℂ)) : ip μ (mulForm ℓ u) w = ip μ u (mulForm ℓ w) := by
  simp only [ip, mulForm_apply, map_mul, Complex.conj_ofReal]
  congr 1; funext x; ring
end GlobalTheory.WrongSignGauss
