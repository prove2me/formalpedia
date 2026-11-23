-- Prove2me | solution 1 for GlobalTheory.Lin.LargeMean.pw_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:06:18.026184+00:00
-- url     : https://prove2.me/submissions/930f5757-b263-4224-adc0-97bd0c890130

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_ZerosDisc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsTsumVonMangoldtDivRpowLeDiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_SummableNonPrimeVonMangoldtDivRpow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_SumPrimesIocEqSumIndicator
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_IntervalIntegrableDivOfBounded
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_LargeMeanOfLargeDerivative

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology GlobalTheory.Lin
open scoped Classical
noncomputable section
open GlobalTheory GlobalTheory.Lin GlobalTheory.Lin.LargeMean
namespace GlobalTheory.Lin.LargeMean
theorem _root_.solution (k : ℕ) {u θ : ℝ} (hu : 0 ≤ u) (hθ : 0 < θ) :
    pw k u ≤ θ ^ k * Real.exp (u / θ - u) := by
  have h := Real.pow_div_factorial_le_exp (u / θ) (by positivity) k
  have e : pw k u = θ ^ k * ((u / θ) ^ k / (k.factorial : ℝ) * Real.exp (-u)) := by
    unfold pw; rw [div_pow]; field_simp
  rw [e, sub_eq_add_neg, Real.exp_add]
  gcongr
end GlobalTheory.Lin.LargeMean
