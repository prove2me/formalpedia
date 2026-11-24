-- Prove2me | solution 1 for GlobalTheory.Lin.LargeMean.abel_pw
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:21:25.233843+00:00
-- url     : https://prove2.me/submissions/14f3be91-d4ec-455f-8141-1781a004619b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_ZerosDisc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsTsumVonMangoldtDivRpowLeDiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_SummableNonPrimeVonMangoldtDivRpow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_SumPrimesIocEqSumIndicator
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_IntervalIntegrableDivOfBounded
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_LargeMeanOfLargeDerivative
import Theorems.Thm_GlobalTheory_Lin_LargeMean_pw_nonneg
import Theorems.Thm_GlobalTheory_Lin_LargeMean_pw_le_one
import Theorems.Thm_GlobalTheory_Lin_LargeMean_hasDerivAt_pw
import Theorems.Thm_GlobalTheory_Lin_LargeMean_continuous_pw
import Theorems.Thm_GlobalTheory_Lin_abel_primesIoc_weight


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
theorem _root_.solution (a : ℕ → ℂ) {r x y : ℝ} (hr : 0 < r) (hx : 1 ≤ x) (hxy : x ≤ y) (m : ℕ) :
    ‖∑ n ∈ primesIoc x y, a n *
        ((pw (m + 1) (r * Real.log n) - pw (m + 1) (r * Real.log y) : ℝ) : ℂ)‖ ≤
      r * ∫ t in x..y, ‖∑ p ∈ primesIoc x t, a p‖ / t := by
  refine GlobalTheory.Lin.abel_primesIoc_weight a (fun t => pw (m + 1) (r * Real.log t))
    (fun t => (pw m (r * Real.log t) - pw (m + 1) (r * Real.log t)) * (r * t⁻¹)) x y r hx hxy
    ?_ ?_ ?_
  · intro t ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    exact (hasDerivAt_pw m _).comp t ((Real.hasDerivAt_log ht0).const_mul r)
  · have hl : ContinuousOn (fun t => r * Real.log t) (Set.Icc x y) :=
      continuousOn_const.mul (continuousOn_id.log fun t ht => by
        have := ht.1; simp only [id]; linarith)
    refine (((continuous_pw m).comp_continuousOn hl).sub
      ((continuous_pw (m + 1)).comp_continuousOn hl)).mul
      (continuousOn_const.mul (continuousOn_id.inv₀ fun t ht => ?_))
    have := ht.1; simp only [id]; linarith
  · intro t ht
    have ht1 : 1 ≤ t := hx.trans ht.1
    have hu : 0 ≤ r * Real.log t := mul_nonneg hr.le (Real.log_nonneg ht1)
    have h1 : |pw m (r * Real.log t) - pw (m + 1) (r * Real.log t)| ≤ 1 := by
      rw [abs_le]
      constructor <;> linarith [pw_nonneg m hu, pw_nonneg (m + 1) hu, pw_le_one m hu,
        pw_le_one (m + 1) hu]
    have h2 : 0 ≤ r * t⁻¹ := by have : 0 < t := by linarith
                                positivity
    rw [abs_mul, abs_of_nonneg h2, div_eq_mul_inv]
    exact mul_le_of_le_one_left h2 h1
end GlobalTheory.Lin.LargeMean
