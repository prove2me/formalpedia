-- Prove2me | solution 1 for GlobalTheory.WrongSignGauss.ip_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:17:53.614198+00:00
-- url     : https://prove2.me/submissions/ce751021-2f58-4bd5-a3ca-31e5289ed266

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SchwartzEqZeroOfWrongSignGaussianRelation

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open SchwartzMap LineDeriv MeasureTheory ComplexConjugate
noncomputable section
open GlobalTheory GlobalTheory.WrongSignGauss
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
variable [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure]
namespace GlobalTheory.WrongSignGauss
theorem _root_.solution (h : 𝓢(V, ℂ)) : ip μ h h = ((∫ x, ‖h x‖ ^ 2 ∂μ : ℝ) : ℂ) := by
  rw [ip]
  first
  | rw [← integral_complex_ofReal]
  | rw [← integral_ofReal (𝕜 := ℂ)]
  congr 1; funext x
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
end GlobalTheory.WrongSignGauss
