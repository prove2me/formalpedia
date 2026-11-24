-- Prove2me | solution 1 for GlobalTheory.Lin.LargeMean.pw_pp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:43:49.611943+00:00
-- url     : https://prove2.me/submissions/03cf655c-9dff-4179-bc41-3ab847f666db

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_ZerosDisc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsTsumVonMangoldtDivRpowLeDiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_SummableNonPrimeVonMangoldtDivRpow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_SumPrimesIocEqSumIndicator
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_IntervalIntegrableDivOfBounded
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_LargeMeanOfLargeDerivative
import Theorems.Thm_GlobalTheory_Lin_LargeMean_pw_le

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
theorem _root_.solution (k : ℕ) {v r : ℝ} (hr : 0 < r) (hv : 0 ≤ v) :
    pw k (r * v) ≤ (4 * r) ^ k * Real.exp (v / 4) := by
  have h1 := pw_le k (u := r * v) (by positivity) (θ := 4 * r) (by positivity)
  refine h1.trans ?_
  have : r * v / (4 * r) = v / 4 := by field_simp
  rw [this]
  gcongr
  have : 0 ≤ r * v := by positivity
  linarith
end GlobalTheory.Lin.LargeMean
