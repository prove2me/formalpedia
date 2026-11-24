-- Prove2me | solution 1 for GlobalTheory.Lin.LargeMean.pw_large
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:44:45.3934+00:00
-- url     : https://prove2.me/submissions/b3e5ed60-1d47-4f7f-a2d1-2f8b8457e8c5

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
theorem _root_.solution (K k : ℕ) {u δ : ℝ} (hδ : 0 < δ) (h : 32 / δ * K ≤ u) (hK : k ≤ 2 * K) :
    pw k u ≤ δ ^ k * Real.exp (-(u / 2)) := by
  have hu : 0 ≤ u := le_trans (by positivity) h
  have h1 := pw_le k hu (θ := 4) (by positivity)
  have hK' : (k : ℝ) ≤ 2 * K := by exact_mod_cast hK
  have h2 : (4 / δ) ^ k ≤ Real.exp (u / 4) := by
    calc (4 / δ) ^ k ≤ Real.exp (4 / δ) ^ k := by
          gcongr; linarith [Real.add_one_le_exp (4 / δ)]
      _ = Real.exp (k * (4 / δ)) := by rw [Real.exp_nat_mul]
      _ ≤ _ := by
          gcongr
          have : k * (4 / δ) ≤ 2 * K * (4 / δ) := by gcongr
          have e : 32 / δ * K = 4 * (2 * K * (4 / δ)) := by ring
          linarith
  have e : Real.exp (-(u / 2)) = Real.exp (u / 4) * Real.exp (u / 4 - u) := by
    rw [← Real.exp_add]; congr 1; ring
  calc _ ≤ _ := h1
    _ = δ ^ k * ((4 / δ) ^ k * Real.exp (u / 4 - u)) := by rw [div_pow]; field_simp
    _ ≤ _ := by rw [e]; gcongr
end GlobalTheory.Lin.LargeMean
