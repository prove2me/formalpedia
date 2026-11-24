-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m87_qpos_factor_post_stopped_reward_shift
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T07:55:48.703896+00:00
-- url     : https://prove2.me/submissions/1d65b78a-4c8e-42f6-8776-181a2265021e

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_B
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_firstUpcrossing_value_eq_threshold
import Theorems.Thm_AvramDividend_Classical_firstBadClock_shift_of_no_early_breach
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_positive_open_clock_eq_all_times
import Theorems.Thm_AvramDividend_Classical_shiftedLevy_increments_right_continuous
set_option autoImplicit false
attribute [local instance] Classical.propDecidable
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal
open Kyprianou.Ch08
open Kyprianou.Ch08.StageB
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {F : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P F)
    (q a x : ℝ) (ha : 0 < a) (hx : 0 ≤ x) (hxa : x ≤ a)
    (A : Set ℝ) (hA : MeasurableSet A)
    (reward : (ℝ≥0 → ℝ) → ℝ≥0∞)
    (hreward_value : ∀ (y : ℝ≥0 → ℝ),
        (∀ t : ℝ≥0, ContinuousWithinAt y (Set.Ici t) t) → y 0 = 0 →
        reward y =
          (∫⁻ s : ℝ≥0, ENNReal.ofReal (Real.exp (-q * (s : ℝ))) *
            (if (s : WithTop ℝ≥0) <
                  tauMinus (fun u (_ : PUnit) => a + y u) 0 () ∧
                a + y s ∈ A
             then (1 : ℝ≥0∞) else 0) ∂positiveTimeLebesgue))
    (ω : Ω)
    (hUL : twoSidedExitUpTime X (a - x) ω < twoSidedExitDownTime X (-x) ω) :
    let U := twoSidedExitUpTime X (a - x)
    let L := twoSidedExitDownTime X (-x)
    let τ : Ω → ℝ≥0 := fun ω => (U ω).toNNReal
    let disc : ℝ≥0 → ℝ≥0∞ := fun t => ENNReal.ofReal (Real.exp (-q * (t : ℝ)))
    let R : ℝ≥0 → Ω → ℝ≥0∞ := fun t ω =>
      if U ω < L ω then disc t *
        (if (t : ℝ≥0∞) < L ω ∧ x + X.X t ω ∈ A then 1 else 0) else 0
    disc (τ ω) * reward (fun s : ℝ≥0 => X.X (τ ω + s) ω - X.X (τ ω) ω) =
      ∫⁻ s : ℝ≥0, R (τ ω + s) ω ∂positiveTimeLebesgue
:= by
  dsimp only
  let U := twoSidedExitUpTime X (a - x) ω
  let L := twoSidedExitDownTime X (-x) ω
  let u := U.toNNReal
  let y : ℝ≥0 → ℝ := fun s => X.X (u + s) ω - X.X u ω
  have hu : (u : ℝ≥0∞) = U := ENNReal.coe_toNNReal (ne_top_of_lt hUL)
  have hv : X.X u ω = a - x :=
    firstUpcrossing_value_eq_threshold X (a - x) (sub_nonneg.mpr hxa) ω u hu
  have hy := shiftedLevy_increments_right_continuous X ω u
  have hy0 : y 0 = 0 := by simp [y]
  have hlevel (s : ℝ≥0) : a + y s = x + X.X (u + s) ω := by
    dsimp [y]
    linarith
  have hpre (s : ℝ≥0) (hs : s < u) : ¬ X.X s ω < -x := by
    intro hb
    have hle : L ≤ (s : ℝ≥0∞) := iInf_le_of_le s (iInf_le _ hb)
    exact (not_lt_of_ge hle) (lt_of_lt_of_le (ENNReal.coe_lt_coe.mpr hs) (hu.trans_le hUL.le))
  have hshift := firstBadClock_shift_of_no_early_breach u
    (fun s => X.X s ω < -x) (fun s => a + y s < 0) hpre
    (fun s => by rw [hlevel, add_comm x, ← lt_sub_iff_add_lt, zero_sub])
  have hclock : (tauMinus (fun s (_ : PUnit) => a + y s) 0 () : ℝ≥0∞) =
      ⨅ (s : ℝ≥0) (_ : a + y s < 0), (s : ℝ≥0∞) := by
    exact source_result81_positive_open_clock_eq_all_times (fun s => a + y s)
      (Iio 0) isOpen_Iio (fun s => continuous_const.continuousWithinAt.add (hy s))
  let c : ℝ≥0∞ := tauMinus (fun s (_ : PUnit) => a + y s) 0 ()
  change c = _ at hclock
  have hL : L = (u : ℝ≥0∞) + c := by rw [hclock]; exact hshift
  rw [hreward_value y hy hy0, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_congr
  intro s
  rw [if_pos hUL]
  have hlt : (s : WithTop ℝ≥0) < tauMinus (fun t (_ : PUnit) => a + y t) 0 () ↔
      ((u + s : ℝ≥0) : ℝ≥0∞) < L := by
    change (s : ℝ≥0∞) < c ↔ _
    rw [hL, ENNReal.coe_add, ENNReal.add_lt_add_iff_left ENNReal.coe_ne_top]
  simp only [hlt]
  simp only [hlevel]
  rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
  congr 2 <;> push_cast <;> ring
