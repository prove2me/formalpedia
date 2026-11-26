-- Prove2me | solution 1 for Kyprianou.Ch04.exercise49RawCompoundDownJumpV5
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T16:12:50.619079+00:00
-- url     : https://prove2.me/submissions/4fbef72b-4666-41b8-82ea-57b40c57195c

import Mathlib
import Theorems.Thm_levy_foundations_compoundDriverInterarrivalPositive
import Theorems.Thm_AvramDividend_Classical_avram_a06_compound_driver_all_marks_negative
import Theorems.Thm_AvramDividend_Classical_avram_a06_original_cp_count_threshold_ae
import Definitions.Def_Kyprianou_Ch04_Exercise4_9Certification
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
import Definitions.Def_levy_foundations_compoundPoisson
import Definitions.Def_levy_foundations_compoundPoissonTripleGivenLevyMeasure
import Definitions.Def_levy_foundations_exponent
open MeasureTheory ProbabilityTheory Set Filter Topology Kyprianou.Ch04 AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Classical Topology
set_option autoImplicit false
theorem solution
    (P : Measure ((ℕ → ℝ) × (ℕ → ℝ))) [IsProbabilityMeasure P]
    (τ Y : ℕ → ((ℕ → ℝ) × (ℕ → ℝ)) → ℝ)
    (h : LevyFoundations.IsCompoundPoissonDriver τ Y (1 : NNReal)
      ((volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0)) P)
    (b : ℝ) (hb : 0 < b) :
    ∀ᵐ w ∂P, ¬ Monotone (fun t : NNReal =>
      LevyFoundations.compoundPoisson b τ Y (t : ℝ) w) := by
  filter_upwards [levy_foundations_compoundDriverInterarrivalPositive h (by norm_num),
    avram_a06_compound_driver_all_marks_negative h,
    avram_a06_original_cp_count_threshold_ae P τ Y h] with w hp hm hk
  let a : ℝ := τ 0 w
  let e : ℝ := min (a/2) (-Y 0 w/(2*b))
  have ha : 0 < a := hp 0
  have he : 0 < e := lt_min (by linarith) (div_pos (by linarith [hm 0]) (by positivity))
  have hea : e ≤ a/2 := min_le_left _ _
  have heb : e ≤ -Y 0 w/(2*b) := min_le_right _ _
  let t : NNReal := ⟨a,ha.le⟩
  let s : NNReal := ⟨a-e,by linarith⟩
  have hst : s ≤ t := by change a-e ≤ a; linarith
  have h0 : LevyFoundations.jumpCount (fun n => LevyFoundations.arrival τ n w) (s : ℝ) = 0 := by
    by_contra hn
    have H := (hk (s : ℝ) 0).1 (Nat.pos_of_ne_zero hn)
    simp [s,a] at H
    change a ≤ a-e at H
    linarith
  have h1 : LevyFoundations.jumpCount (fun n => LevyFoundations.arrival τ n w) (t : ℝ) = 1 := by
    have H := (hk (t : ℝ) 0).2 (by simp [t,a]; exact le_rfl)
    have H' : ¬ 1 < LevyFoundations.jumpCount (fun n => LevyFoundations.arrival τ n w) (t : ℝ) := by
      intro hc
      have hh := (hk (t : ℝ) 1).1 hc
      simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add] at hh
      change a + τ 1 w ≤ a at hh
      linarith [hp 1]
    omega
  intro hmono
  have H := hmono hst
  unfold LevyFoundations.compoundPoisson LevyFoundations.piecewisePath at H
  dsimp only at H
  rw [h0,h1] at H
  simp only [Finset.sum_range_zero,Finset.sum_range_one,zero_add,add_zero] at H
  change b * (a-e) ≤ b*a + Y 0 w at H
  have heB := (le_div_iff₀ (show 0 < 2*b by positivity)).1 heb
  nlinarith [hm 0]
