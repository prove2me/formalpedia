-- Prove2me | solution 1 for MasulloRH.dyadic_profile_log_integral_and_divergence
-- status  : ACCEPTED   (prove)
-- author  : @Yi
-- created : 2026-11-21T01:26:03.72327+00:00
-- url     : https://prove2.me/submissions/79373855-54b9-48d6-b32c-edf28b012aca

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open Filter MeasureTheory Set
open scoped Topology

theorem solution (b G : ℝ → ℝ) (hb : Continuous b)
    (hpiece : ∀ k : ℕ, ∀ t ∈ Icc ((1/2:ℝ)^(k+1)) ((1/2:ℝ)^k),
      G t = (1/2:ℝ)*b ((2:ℝ)^(k+1)*t)) :
    (∀ m : ℕ, (∫ t in (1/2:ℝ)^m..1, G t/t) = (m:ℝ)/2 * ∫ u in (1:ℝ)..2, b u/u) ∧
    (0 < (∫ u in (1:ℝ)..2, b u/u) →
      Tendsto (fun m : ℕ => ∫ t in (1/2:ℝ)^m..1, G t/t) atTop atTop ∧
      ¬ IntegrableOn (fun t : ℝ => G t/t) (Ioc 0 1)) := by
  let x (k : ℕ) : ℝ := (1/2:ℝ)^k
  let c (k : ℕ) : ℝ := (2:ℝ)^(k+1)
  let I : ℝ := ∫ u in (1:ℝ)..2, b u/u
  have hx (k : ℕ) : 0 < x k := by dsimp [x]; positivity
  have hc (k : ℕ) : 0 < c k := by dsimp [c]; positivity
  have hle (k : ℕ) : x (k+1) ≤ x k := by
    change (1/2:ℝ)^(k+1) ≤ (1/2:ℝ)^k
    rw [pow_succ]
    nlinarith [hx k]
  have hL (k : ℕ) : c k * x (k+1) = 1 := by simp [c,x]
  have hR (k : ℕ) : c k * x k = 2 := by
    change (2:ℝ)^(k+1) * (1/2:ℝ)^k = 2
    rw [one_div_pow, pow_succ]
    field_simp
  have shell_int (k : ℕ) : IntervalIntegrable (fun t : ℝ => G t/t) volume (x (k+1)) (x k) := by
    apply ContinuousOn.intervalIntegrable_of_Icc (hle k)
    have ha : Continuous (fun t : ℝ => (1/2:ℝ)*b (c k*t)) :=
      continuous_const.mul (hb.comp (continuous_const.mul continuous_id))
    apply (ha.continuousOn.div continuousOn_id (fun t ht => ne_of_gt ((hx _).trans_le ht.1))).congr
    intro t ht
    change G t/t = (1/2:ℝ)*b ((2:ℝ)^(k+1)*t)/t
    rw [hpiece k t ht]
  have shell (k : ℕ) : (∫ t in x (k+1)..x k, G t/t) = I/2 := by
    calc
      _ = ∫ t in x (k+1)..x k, (c k/2)*((fun u : ℝ => b u/u) (c k*t)) := by
        apply intervalIntegral.integral_congr
        rw [uIcc_of_le (hle k)]
        intro t ht
        have htpos : 0 < t := (hx _).trans_le ht.1
        change G t/t = c k/2*(b (c k*t)/(c k*t))
        rw [hpiece k t ht]
        have hk : c k ≠ 0 := (hc k).ne'
        change (1/2:ℝ)*b (c k*t)/t = c k/2*(b (c k*t)/(c k*t))
        field_simp
      _ = _ := by
        rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_mul_left (fun u : ℝ => b u/u) (hc k).ne',
          hL, hR, smul_eq_mul]
        change c k/2*((c k)⁻¹*I)=I/2
        have hk := (hc k).ne'
        field_simp
  have accum (m : ℕ) :
      IntervalIntegrable (fun t : ℝ => G t/t) volume (x m) 1 ∧
      (∫ t in x m..1, G t/t) = (m:ℝ)/2*I := by
    induction m with
    | zero => simp [x]
    | succ m ih =>
      refine ⟨(shell_int m).trans ih.1, ?_⟩
      rw [← intervalIntegral.integral_add_adjacent_intervals (shell_int m) ih.1, shell, ih.2]
      push_cast
      ring
  refine ⟨fun m => (accum m).2, ?_⟩
  intro hI
  have hi : 0 < I/2 := by change 0<I at hI; positivity
  have ht : Tendsto (fun m : ℕ => ∫ t in x m..1, G t/t) atTop atTop := by
    apply (Tendsto.const_mul_atTop hi (tendsto_natCast_atTop_atTop (R:=ℝ))).congr'
    filter_upwards with m
    rw [(accum m).2]
    ring
  refine ⟨ht, ?_⟩
  intro hint
  let M : ℝ := ∫ t in Ioc (0:ℝ) 1, ‖G t/t‖
  have hbound (m : ℕ) : (∫ t in x m..1, G t/t) ≤ M := by
    have hx1 : x m ≤ 1 := pow_le_one₀ (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num)
    rw [intervalIntegral.integral_of_le hx1]
    calc
      _ ≤ ‖∫ t in Ioc (x m) 1, G t/t‖ := le_abs_self _
      _ ≤ ∫ t in Ioc (x m) 1, ‖G t/t‖ := norm_integral_le_integral_norm _
      _ ≤ M := setIntegral_mono_set hint.norm (Filter.Eventually.of_forall fun t => norm_nonneg _)
        (Filter.Eventually.of_forall (fun t ht => Ioc_subset_Ioc (hx m).le le_rfl ht))
  obtain ⟨m,hm⟩ := (ht.eventually_gt_atTop M).exists
  exact (not_lt_of_ge (hbound m)) hm
