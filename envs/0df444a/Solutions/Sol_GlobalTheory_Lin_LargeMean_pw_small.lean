-- Prove2me | solution 1 for GlobalTheory.Lin.LargeMean.pw_small
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:43:50.41511+00:00
-- url     : https://prove2.me/submissions/1ca172fe-2db8-4d2f-bd89-15117b0c844c

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
theorem _root_.solution (K k : ℕ) {u δ : ℝ} (hδ : 0 < δ) (hu : 0 ≤ u) (h : u ≤ δ / 3 * K) (hK : K ≤ k) :
    pw k u ≤ δ ^ k * Real.exp (-(u / 2)) := by
  have h1 := pw_le k hu (θ := δ / 3) (by positivity)
  have h2 : u / (δ / 3) ≤ k := by
    rw [div_le_iff₀ (by positivity)]
    have : (K : ℝ) ≤ k := by exact_mod_cast hK
    nlinarith
  have h3 : Real.exp (u / (δ / 3) - u) ≤ 3 ^ k * Real.exp (-(u / 2)) := by
    have h4 : Real.exp k ≤ 3 ^ k := by
      rw [← mul_one (k : ℝ), Real.exp_nat_mul]
      gcongr
      exact (Real.exp_one_lt_d9.trans (by norm_num)).le
    calc _ ≤ Real.exp (k + -(u / 2)) := by gcongr; linarith
      _ ≤ _ := by rw [Real.exp_add]; gcongr
  calc _ ≤ (δ / 3) ^ k * (3 ^ k * Real.exp (-(u / 2))) := h1.trans (by gcongr)
    _ = _ := by rw [div_pow]; field_simp
end GlobalTheory.Lin.LargeMean
