-- Prove2me | solution 1 for GlobalTheory.Lin.LargeMean.norm_tsum_le_of_close
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:45:10.823924+00:00
-- url     : https://prove2.me/submissions/fcb24b8d-4693-490d-8bbf-570940a09cf3

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
theorem _root_.solution {T P : ℕ → ℂ} {G : ℕ → ℝ} (hP : Summable P)
    (hG : Summable G) (h : ∀ n, ‖T n - P n‖ ≤ G n) :
    ‖∑' n, T n‖ ≤ ‖∑' n, P n‖ + ∑' n, G n := by
  have h1 : Summable fun n => T n - P n := Summable.of_norm_bounded hG h
  have h2 : ∑' n, T n = ∑' n, P n + ∑' n, (T n - P n) := by
    rw [← hP.tsum_add h1]; simp
  rw [h2]
  refine (norm_add_le _ _).trans ?_
  gcongr
  exact tsum_of_norm_bounded hG.hasSum h
end GlobalTheory.Lin.LargeMean
