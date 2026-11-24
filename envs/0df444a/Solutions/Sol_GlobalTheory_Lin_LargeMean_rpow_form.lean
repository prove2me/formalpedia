-- Prove2me | solution 1 for GlobalTheory.Lin.LargeMean.rpow_form
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:43:51.406327+00:00
-- url     : https://prove2.me/submissions/7f3e68ce-03c0-46e4-8b8b-8971971cedd8

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
theorem _root_.solution (n : ℕ) (hn : 0 < n) (s x : ℝ) :
    x / (n : ℝ) ^ (1 + s) = x / n * Real.exp (-(s * Real.log n)) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [Real.rpow_add hn', Real.rpow_one, Real.rpow_def_of_pos hn', Real.exp_neg, mul_comm s]
  field_simp
end GlobalTheory.Lin.LargeMean
