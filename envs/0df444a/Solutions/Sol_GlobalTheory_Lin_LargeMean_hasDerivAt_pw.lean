-- Prove2me | solution 1 for GlobalTheory.Lin.LargeMean.hasDerivAt_pw
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:42:41.836137+00:00
-- url     : https://prove2.me/submissions/d2a8f49f-324b-45d0-9e8e-e3a9f019b5d9

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
theorem _root_.solution (m : ℕ) (u : ℝ) : HasDerivAt (pw (m + 1)) (pw m u - pw (m + 1) u) u := by
  have h1 := ((hasDerivAt_pow (m + 1) u).div_const ((m + 1).factorial : ℝ)).mul
    (hasDerivAt_neg u).exp
  refine HasDerivAt.congr_deriv (f := pw (m + 1)) h1 ?_
  unfold pw
  rw [Nat.factorial_succ]
  simp only [Nat.add_sub_cancel]
  push_cast
  field_simp
  ring
end GlobalTheory.Lin.LargeMean
