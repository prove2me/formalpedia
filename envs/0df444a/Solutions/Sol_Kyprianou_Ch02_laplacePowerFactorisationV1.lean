-- Prove2me | solution 1 for Kyprianou.Ch02.laplacePowerFactorisationV1
-- status  : ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-24T02:02:18.45013+00:00
-- url     : https://prove2.me/submissions/16aeddfc-4981-4384-817b-1162965aa93e

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess

open Filter Set Topology Metric
open scoped Topology
set_option autoImplicit false
set_option linter.unusedVariables false

/-- If `c n ∈ [0,1]` and `c n ^ (n+1) → γ > 0`, then `c → 1`. -/
private theorem tendsto_one_of_pow_tendsto_pos
    (c : ℕ → ℝ) (γ : ℝ)
    (hc0 : ∀ n, 0 ≤ c n) (hc1 : ∀ n, c n ≤ 1)
    (hγ : 0 < γ) (hC : Tendsto (fun n => c n ^ (n + 1)) atTop (nhds γ)) :
    Tendsto c atTop (nhds (1 : ℝ)) := by
  rw [Metric.tendsto_atTop]
  intro ε εpos
  -- Reduce to ε' ∈ (0,1)
  set ε' : ℝ := min ε (1 / 2) with hε'
  have ε'pos : 0 < ε' := lt_min εpos (by norm_num)
  have ε'le : ε' ≤ ε := min_le_left _ _
  have ε'lt1 : ε' < 1 := (min_le_right _ _).trans_lt (by norm_num)
  have h1ε0 : 0 ≤ 1 - ε' := by linarith
  have h1ε1 : 1 - ε' < 1 := by linarith
  have hpow0 : Tendsto (fun n : ℕ => (1 - ε') ^ (n + 1)) atTop (nhds 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one h1ε0 h1ε1).comp (tendsto_add_atTop_nat 1)
  have hpos : ∀ᶠ n in atTop, γ / 2 < c n ^ (n + 1) :=
    hC.eventually (eventually_gt_nhds (half_lt_self hγ))
  have hsmall : ∀ᶠ n in atTop, (1 - ε') ^ (n + 1) < γ / 2 :=
    hpow0.eventually (eventually_lt_nhds (half_pos hγ))
  have hEv : ∀ᶠ n in atTop, dist (c n) 1 < ε := by
    filter_upwards [hpos, hsmall] with n hcn hεn
    have hball : |c n - 1| = 1 - c n := by
      rw [← neg_sub, abs_neg, abs_of_nonneg (sub_nonneg.mpr (hc1 n))]
    rw [dist_eq_norm, Real.norm_eq_abs, hball]
    have : 1 - ε' < c n := by
      by_contra! hle
      have : c n ^ (n + 1) ≤ (1 - ε') ^ (n + 1) :=
        pow_le_pow_left₀ (hc0 n) hle (n + 1)
      linarith
    have : 1 - c n < ε' := by linarith
    exact this.trans_le ε'le
  exact eventually_atTop.1 hEv

theorem solution
    (a b : ℕ → ℝ) (α β : ℝ)
    (ha : ∀ n, a n ∈ Set.Icc 0 1) (hb : ∀ n, b n ∈ Set.Icc 0 1)
    (hc : ∀ n, 0 ≤ a n + b n - 1)
    (hα : 0 < α) (hβ : 0 < β)
    (hA : Tendsto (fun n => a n ^ (n + 1)) atTop (nhds α))
    (hB : Tendsto (fun n => b n ^ (n + 1)) atTop (nhds β)) :
    Tendsto (fun n => (a n + b n - 1) ^ (n + 1)) atTop (nhds (α * β)) := by
  have ha0 (n : ℕ) : 0 ≤ a n := (ha n).1
  have ha1 (n : ℕ) : a n ≤ 1 := (ha n).2
  have hb0 (n : ℕ) : 0 ≤ b n := (hb n).1
  have hb1 (n : ℕ) : b n ≤ 1 := (hb n).2
  have ha_to1 := tendsto_one_of_pow_tendsto_pos a α ha0 ha1 hα hA
  have hb_to1 := tendsto_one_of_pow_tendsto_pos b β hb0 hb1 hβ hB
  have hprod : Tendsto (fun n => (a n * b n) ^ (n + 1)) atTop (nhds (α * β)) := by
    convert hA.mul hB using 1
    funext n; exact mul_pow (a n) (b n) (n + 1)
  have hgap_nonneg (n : ℕ) :
      0 ≤ (a n * b n) ^ (n + 1) - (a n + b n - 1) ^ (n + 1) := by
    set x := a n + b n - 1
    set y := a n * b n
    have hx0 : 0 ≤ x := hc n
    have hxy : x ≤ y := by
      have : 0 ≤ (1 - a n) * (1 - b n) :=
        mul_nonneg (sub_nonneg.mpr (ha1 n)) (sub_nonneg.mpr (hb1 n))
      linarith [show y - x = (1 - a n) * (1 - b n) by ring]
    exact sub_nonneg.mpr (pow_le_pow_left₀ hx0 hxy (n + 1))
  have hgap_le (n : ℕ) :
      (a n * b n) ^ (n + 1) - (a n + b n - 1) ^ (n + 1) ≤
        (↑(n + 1) : ℝ) * ((1 - a n) * (1 - b n)) := by
    set x := a n + b n - 1
    set y := a n * b n
    have hx0 : 0 ≤ x := hc n
    have hy0 : 0 ≤ y := mul_nonneg (ha0 n) (hb0 n)
    have hyx : y - x = (1 - a n) * (1 - b n) := by ring
    have hxy : x ≤ y := by
      have : 0 ≤ (1 - a n) * (1 - b n) :=
        mul_nonneg (sub_nonneg.mpr (ha1 n)) (sub_nonneg.mpr (hb1 n))
      linarith
    have hy1 : y ≤ 1 := mul_le_one₀ (ha1 n) (hb0 n) (hb1 n)
    have hnonneg := hgap_nonneg n
    have hpow : |y ^ (n + 1) - x ^ (n + 1)| ≤
        |y - x| * (↑(n + 1) : ℝ) * max |y| |x| ^ ((n + 1) - 1) :=
      abs_pow_sub_pow_le y x (n + 1)
    simp only [Nat.add_one_sub_one] at hpow
    have hmain : y ^ (n + 1) - x ^ (n + 1) ≤
        |y - x| * (↑(n + 1) : ℝ) * max |y| |x| ^ n := by
      rwa [abs_of_nonneg hnonneg] at hpow
    have hmax1 : max |y| |x| ≤ 1 := by
      simp only [abs_of_nonneg hy0, abs_of_nonneg hx0]
      exact max_le hy1 (hxy.trans hy1)
    have hmaxpow : max |y| |x| ^ n ≤ (1 : ℝ) :=
      pow_le_one₀ (n := n) (le_trans (abs_nonneg _) (le_max_left _ _)) hmax1
    have hyxabs : |y - x| = (1 - a n) * (1 - b n) := by
      rw [hyx, abs_of_nonneg
        (mul_nonneg (sub_nonneg.mpr (ha1 n)) (sub_nonneg.mpr (hb1 n)))]
    calc
      y ^ (n + 1) - x ^ (n + 1)
          ≤ |y - x| * (↑(n + 1) : ℝ) * max |y| |x| ^ n := hmain
      _ ≤ |y - x| * (↑(n + 1) : ℝ) * (1 : ℝ) :=
          mul_le_mul_of_nonneg_left hmaxpow (mul_nonneg (abs_nonneg _) (Nat.cast_nonneg _))
      _ = (↑(n + 1) : ℝ) * ((1 - a n) * (1 - b n)) := by
          rw [hyxabs, mul_one, mul_comm]
  have hgap0 :
      Tendsto (fun n : ℕ => (↑(n + 1) : ℝ) * ((1 - a n) * (1 - b n))) atTop (nhds 0) := by
    let C : ℝ := -Real.log (α / 2) + 1
    have ha_pos : ∀ᶠ n in atTop, 0 < a n :=
      ha_to1.eventually (eventually_gt_nhds (by norm_num : (0 : ℝ) < 1))
    have hApos : ∀ᶠ n in atTop, α / 2 < a n ^ (n + 1) :=
      hA.eventually (eventually_gt_nhds (half_lt_self hα))
    have hbound : ∀ᶠ n : ℕ in atTop, (↑(n + 1) : ℝ) * (1 - a n) ≤ C := by
      filter_upwards [ha_pos, hApos] with n hapos hpow
      have h1a : 1 - a n ≤ -Real.log (a n) := by
        linarith [Real.log_le_sub_one_of_pos hapos]
      calc
        (↑(n + 1) : ℝ) * (1 - a n) ≤ (↑(n + 1) : ℝ) * (-Real.log (a n)) :=
          mul_le_mul_of_nonneg_left h1a (Nat.cast_nonneg _)
        _ = -((↑(n + 1) : ℝ) * Real.log (a n)) := by ring
        _ = -Real.log (a n ^ (n + 1)) := by rw [Real.log_pow]
        _ ≤ -Real.log (α / 2) := by
          linarith [Real.log_lt_log (half_pos hα) hpow]
        _ ≤ C := by simp [C]
    have hb1tend : Tendsto (fun n => 1 - b n) atTop (nhds (0 : ℝ)) := by
      simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub hb_to1
    have hCtend : Tendsto (fun n => C * (1 - b n)) atTop (nhds (0 : ℝ)) := by
      simpa using (tendsto_const_nhds (x := C)).mul hb1tend
    refine squeeze_zero'
      (Eventually.of_forall fun n : ℕ =>
        mul_nonneg (Nat.cast_nonneg _)
          (mul_nonneg (sub_nonneg.mpr (ha1 n)) (sub_nonneg.mpr (hb1 n))))
      ?_ hCtend
    filter_upwards [hbound] with n hbnd
    have h1b : 0 ≤ 1 - b n := sub_nonneg.mpr (hb1 n)
    calc
      (↑(n + 1) : ℝ) * ((1 - a n) * (1 - b n))
          = ((↑(n + 1) : ℝ) * (1 - a n)) * (1 - b n) := by ring
      _ ≤ C * (1 - b n) := mul_le_mul_of_nonneg_right hbnd h1b
  have hdiff0 :
      Tendsto (fun n =>
        (a n * b n) ^ (n + 1) - (a n + b n - 1) ^ (n + 1)) atTop (nhds 0) :=
    squeeze_zero' (Eventually.of_forall hgap_nonneg)
      (Eventually.of_forall hgap_le) hgap0
  have hfinal := hprod.sub hdiff0
  convert hfinal using 1
  · funext n; abel
  · simp
