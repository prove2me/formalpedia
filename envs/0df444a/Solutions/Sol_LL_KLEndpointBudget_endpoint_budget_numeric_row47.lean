-- Prove2me | solution 1 for LL_KLEndpointBudget.endpoint_budget_numeric_row47
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T23:50:58.518821+00:00
-- url     : https://prove2.me/submissions/f0b1b1b2-52a2-443e-bba1-1cf206cced08

import Mathlib
import Definitions.Def_LL_KLEndpointBudget_PrintedRow
import Definitions.Def_LL_KLEndpointBudget_evenBase
import Definitions.Def_LL_KLEndpointBudget_PrintedRow_threshold
import Definitions.Def_LL_KLEndpointBudget_PrintedRow_deltaQ
import Definitions.Def_LL_KLEndpointBudget_PrintedRow_uQ
import Definitions.Def_LL_KLEndpointBudget_rowEndpointX
import Definitions.Def_LL_KLEndpointBudget_lowZeroBudget
import Definitions.Def_LL_KLEndpointBudget_highZeroBudget
import Definitions.Def_LL_KLEndpointBudget_PrintedRow_aQ
import Definitions.Def_LL_KLEndpointBudget_weight
import Definitions.Def_LL_KLEndpointBudget_tailMass
import Definitions.Def_LL_KLEndpointBudget_tailCoefficient

open Real Set MeasureTheory LL_KLEndpointBudget

private def betaNum : ℕ → ℕ
  | 0 => 1
  | m + 1 => (2 * m + 2) * betaNum m

private def betaDen : ℕ → ℕ
  | 0 => 1
  | m + 1 => (2 * m + 3) * betaDen m

private lemma betaNum_pos (m : ℕ) : 0 < betaNum m := by
  induction m with
  | zero => decide
  | succ m ih => exact Nat.mul_pos (by omega) ih

private lemma betaDen_pos (m : ℕ) : 0 < betaDen m := by
  induction m with
  | zero => decide
  | succ m ih => exact Nat.mul_pos (by omega) ih

private noncomputable def S5 (m : ℕ) (u : ℝ) : ℝ :=
  1 - (m.choose 1 : ℝ) * u + (m.choose 2 : ℝ) * u ^ 2 - (m.choose 3 : ℝ) * u ^ 3 +
    (m.choose 4 : ℝ) * u ^ 4 - (m.choose 5 : ℝ) * u ^ 5

private noncomputable def P5 (m : ℕ) (t : ℝ) : ℝ :=
  (2 * t - 1) / 2
    - (m.choose 1 : ℝ) * (2 * t - 1) ^ 3 / 6
    + (m.choose 2 : ℝ) * (2 * t - 1) ^ 5 / 10
    - (m.choose 3 : ℝ) * (2 * t - 1) ^ 7 / 14
    + (m.choose 4 : ℝ) * (2 * t - 1) ^ 9 / 18
    - (m.choose 5 : ℝ) * (2 * t - 1) ^ 11 / 22

private lemma one_sub_pow_ge_S5 (m : ℕ) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    S5 m u ≤ (1 - u) ^ m := by
  induction m with
  | zero => simp [S5]
  | succ m ih =>
    have hmul : (1 - u) * S5 m u ≤ (1 - u) ^ (m + 1) := by
      rw [pow_succ']
      exact mul_le_mul_of_nonneg_left ih (by linarith)
    have hstep : S5 (m + 1) u ≤ (1 - u) * S5 m u := by
      have hc1 : ((m + 1).choose 1 : ℝ) = (m.choose 0 : ℝ) + (m.choose 1 : ℝ) := by exact_mod_cast Nat.choose_succ_succ m 0
      have hc2 : ((m + 1).choose 2 : ℝ) = (m.choose 1 : ℝ) + (m.choose 2 : ℝ) := by exact_mod_cast Nat.choose_succ_succ m 1
      have hc3 : ((m + 1).choose 3 : ℝ) = (m.choose 2 : ℝ) + (m.choose 3 : ℝ) := by exact_mod_cast Nat.choose_succ_succ m 2
      have hc4 : ((m + 1).choose 4 : ℝ) = (m.choose 3 : ℝ) + (m.choose 4 : ℝ) := by exact_mod_cast Nat.choose_succ_succ m 3
      have hc5 : ((m + 1).choose 5 : ℝ) = (m.choose 4 : ℝ) + (m.choose 5 : ℝ) := by exact_mod_cast Nat.choose_succ_succ m 4
      have hc0 : (m.choose 0 : ℝ) = 1 := by norm_num
      have hdiff : (1 - u) * S5 m u - S5 (m + 1) u = (m.choose 5 : ℝ) * u ^ 6 := by
        unfold S5
        rw [hc1, hc2, hc3, hc4, hc5, hc0]
        ring
      have hnn : 0 ≤ (m.choose 5 : ℝ) * u ^ 6 := mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hu0 6)
      linarith
    exact le_trans hstep hmul

private lemma continuous_weight (m : ℕ) : Continuous (weight m) := by
  unfold weight
  continuity

private lemma integral_weight_zero_one (m : ℕ) :
    (∫ t in (0 : ℝ)..1, weight m t) = (betaNum m : ℝ) / (betaDen m : ℝ) := by
  induction m with
  | zero =>
    simp [weight, betaNum, betaDen]
  | succ m ih =>
    let Q : ℝ → ℝ := fun t => (2 * t - 1) * (4 * t * (1 - t)) ^ (m + 1)
    have hderiv : ∀ t ∈ uIcc (0 : ℝ) 1,
        HasDerivAt Q ((4 * (m : ℝ) + 6) * weight (m + 1) t - (4 * (m : ℝ) + 4) * weight m t) t := by
      intro t _
      have h1 : HasDerivAt (fun x : ℝ => 2 * x - 1) 2 t := by
        exact (((hasDerivAt_id t).const_mul (2 : ℝ)).sub_const (1 : ℝ)).congr_deriv (by ring)
      have h2 : HasDerivAt (fun x : ℝ => 4 * x * (1 - x)) (4 - 8 * t) t := by
        have ha : HasDerivAt (fun x : ℝ => 4 * x) 4 t :=
          ((hasDerivAt_id t).const_mul (4 : ℝ)).congr_deriv (by ring)
        have hb : HasDerivAt (fun x : ℝ => 1 - x) (-1) t :=
          (hasDerivAt_id t).const_sub (1 : ℝ)
        exact (ha.mul hb).congr_deriv (by ring)
      have h3 : HasDerivAt (fun x : ℝ => (4 * x * (1 - x)) ^ (m + 1))
          (((m + 1 : ℕ) : ℝ) * (4 * t * (1 - t)) ^ m * (4 - 8 * t)) t := by
        exact (show HasDerivAt (fun x : ℝ => (4 * x * (1 - x)) ^ (m + 1)) _ t from h2.pow (m + 1)).congr_deriv
          (by simp)
      exact (show HasDerivAt Q _ t from h1.mul h3).congr_deriv (by
        unfold weight
        push_cast
        rw [pow_succ]
        ring)
    have hint1 : IntervalIntegrable (fun t => (4 * (m : ℝ) + 6) * weight (m + 1) t) volume 0 1 :=
      ((continuous_weight (m + 1)).const_mul _).intervalIntegrable 0 1
    have hint0 : IntervalIntegrable (fun t => (4 * (m : ℝ) + 4) * weight m t) volume 0 1 :=
      ((continuous_weight m).const_mul _).intervalIntegrable 0 1
    have hftc : (∫ t in (0 : ℝ)..1,
        ((4 * (m : ℝ) + 6) * weight (m + 1) t - (4 * (m : ℝ) + 4) * weight m t)) = Q 1 - Q 0 :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hint1.sub hint0)
    have hQ : Q 1 - Q 0 = 0 := by simp [Q]
    rw [hQ, intervalIntegral.integral_sub hint1 hint0,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, ih] at hftc
    simp only [betaNum, betaDen, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat]
    have hbd0 : (betaDen m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (betaDen_pos m).ne'
    have hden1 : (4 * (m : ℝ) + 6) ≠ 0 := by positivity
    have hden2 : (2 * (m : ℝ) + 3) ≠ 0 := by positivity
    field_simp at hftc ⊢
    linarith

private lemma hasDerivAt_P5 (m : ℕ) (t : ℝ) :
    HasDerivAt (P5 m) (S5 m ((2 * t - 1) ^ 2)) t := by
  have hu : HasDerivAt (fun x : ℝ => 2 * x - 1) 2 t :=
    (((hasDerivAt_id t).const_mul (2 : ℝ)).sub_const (1 : ℝ)).congr_deriv (by ring)
  have hp3 : HasDerivAt (fun x : ℝ => (2 * x - 1) ^ 3) (((3 : ℕ) : ℝ) * (2 * t - 1) ^ 2 * 2) t :=
    hu.pow 3
  have hp5 : HasDerivAt (fun x : ℝ => (2 * x - 1) ^ 5) (((5 : ℕ) : ℝ) * (2 * t - 1) ^ 4 * 2) t :=
    hu.pow 5
  have hp7 : HasDerivAt (fun x : ℝ => (2 * x - 1) ^ 7) (((7 : ℕ) : ℝ) * (2 * t - 1) ^ 6 * 2) t :=
    hu.pow 7
  have hp9 : HasDerivAt (fun x : ℝ => (2 * x - 1) ^ 9) (((9 : ℕ) : ℝ) * (2 * t - 1) ^ 8 * 2) t :=
    hu.pow 9
  have hp11 : HasDerivAt (fun x : ℝ => (2 * x - 1) ^ 11) (((11 : ℕ) : ℝ) * (2 * t - 1) ^ 10 * 2) t :=
    hu.pow 11
  have hraw : HasDerivAt (P5 m) _ t :=
    ((((((hu.div_const 2).sub (((hp3.const_mul (m.choose 1 : ℝ)).div_const 6))).add
      (((hp5.const_mul (m.choose 2 : ℝ)).div_const 10))).sub
      (((hp7.const_mul (m.choose 3 : ℝ)).div_const 14))).add
      (((hp9.const_mul (m.choose 4 : ℝ)).div_const 18))).sub
      (((hp11.const_mul (m.choose 5 : ℝ)).div_const 22)))
  exact hraw.congr_deriv (by unfold S5; push_cast; ring)

private lemma tailMass_nonneg (m : ℕ) {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1 / 2) :
    0 ≤ tailMass m a := by
  unfold tailMass
  have h1 : 0 ≤ ∫ t in (0 : ℝ)..a, weight m t := by
    apply intervalIntegral.integral_nonneg ha0
    intro t ht
    unfold weight
    exact pow_nonneg (by nlinarith [ht.1, ht.2]) m
  have h2 : 0 ≤ ∫ t in (1 - a)..1, weight m t := by
    apply intervalIntegral.integral_nonneg (by linarith)
    intro t ht
    unfold weight
    exact pow_nonneg (by nlinarith [ht.1, ht.2]) m
  linarith

private lemma tailMass_div_le (m : ℕ) {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1 / 2) :
    tailMass m a / (∫ t in (0 : ℝ)..1, weight m t) ≤
      1 - (P5 m (1 - a) - P5 m a) / ((betaNum m : ℝ) / (betaDen m : ℝ)) := by
  have hw := continuous_weight m
  have hadj1 := intervalIntegral.integral_add_adjacent_intervals
    (hw.intervalIntegrable (μ := volume) 0 a) (hw.intervalIntegrable (μ := volume) a (1 - a))
  have hadj2 := intervalIntegral.integral_add_adjacent_intervals
    (hw.intervalIntegrable (μ := volume) 0 (1 - a)) (hw.intervalIntegrable (μ := volume) (1 - a) 1)
  have hdecomp : tailMass m a = (∫ t in (0 : ℝ)..1, weight m t) - (∫ t in a..(1 - a), weight m t) := by
    unfold tailMass
    linarith
  have hS5_cont : Continuous (fun t : ℝ => S5 m ((2 * t - 1) ^ 2)) := by
    unfold S5
    continuity
  have hS5_int : IntervalIntegrable (fun t : ℝ => S5 m ((2 * t - 1) ^ 2)) volume a (1 - a) :=
    hS5_cont.intervalIntegrable (μ := volume) a (1 - a)
  have hftc : (∫ t in a..(1 - a), S5 m ((2 * t - 1) ^ 2)) = P5 m (1 - a) - P5 m a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hasDerivAt_P5 m t) hS5_int
  have hmono : (∫ t in a..(1 - a), S5 m ((2 * t - 1) ^ 2)) ≤ ∫ t in a..(1 - a), weight m t := by
    apply intervalIntegral.integral_mono_on (by linarith) hS5_int (hw.intervalIntegrable (μ := volume) a (1 - a))
    intro t ht
    have ht0 : 0 ≤ t := by linarith [ht.1]
    have ht1 : t ≤ 1 := by linarith [ht.2]
    have hu0 : 0 ≤ (2 * t - 1) ^ 2 := sq_nonneg _
    have hu1 : (2 * t - 1) ^ 2 ≤ 1 := by nlinarith
    have hge := one_sub_pow_ge_S5 m hu0 hu1
    have hid : 1 - (2 * t - 1) ^ 2 = 4 * t * (1 - t) := by ring
    unfold weight
    rwa [← hid]
  have hbeta := integral_weight_zero_one m
  have hbpos : 0 < (betaNum m : ℝ) / (betaDen m : ℝ) :=
    div_pos (Nat.cast_pos.mpr (betaNum_pos m)) (Nat.cast_pos.mpr (betaDen_pos m))
  rw [hdecomp, hbeta, sub_div, div_self hbpos.ne']
  have hdiv : (P5 m (1 - a) - P5 m a) / ((betaNum m : ℝ) / (betaDen m : ℝ)) ≤
      (∫ t in a..(1 - a), weight m t) / ((betaNum m : ℝ) / (betaDen m : ℝ)) :=
    div_le_div_of_nonneg_right (by linarith) hbpos.le
  linarith

private lemma exp_one_bounds :
    (271828 / 100000 : ℝ) ≤ Real.exp 1 ∧ Real.exp 1 ≤ (271829 / 100000 : ℝ) := by
  constructor
  · linarith [Real.exp_one_gt_d9]
  · linarith [Real.exp_one_lt_d9]

private lemma exp_le_inv_one_sub {u : ℝ} (hu : u < 1) : Real.exp u ≤ 1 / (1 - u) := by
  have h1 : -u + 1 ≤ Real.exp (-u) := Real.add_one_le_exp (-u)
  rw [Real.exp_neg] at h1
  have hpos : 0 < 1 - u := by linarith
  have hepos : 0 < Real.exp u := Real.exp_pos u
  rw [le_div_iff₀' hpos]
  calc (1 - u) * Real.exp u = (-u + 1) * Real.exp u := by ring
    _ ≤ (Real.exp u)⁻¹ * Real.exp u := mul_le_mul_of_nonneg_right h1 hepos.le
    _ = 1 := inv_mul_cancel₀ hepos.ne'

private lemma exp_dyadic_upper (n p : ℕ) (hp : (p : ℝ) < 1024) :
    Real.exp ((n : ℝ) + (p : ℝ) / 32) ≤
      (271829 / 100000 : ℝ) ^ n * (1024 / (1024 - (p : ℝ))) ^ 32 := by
  rw [Real.exp_add]
  have hn : Real.exp (n : ℝ) ≤ (271829 / 100000 : ℝ) ^ n := by
    have h1 : Real.exp (n : ℝ) = (Real.exp 1) ^ n := by
      rw [← Real.exp_nat_mul]
      simp
    rw [h1]
    exact pow_le_pow_left₀ (Real.exp_pos 1).le exp_one_bounds.2 n
  have hp_eq : Real.exp ((p : ℝ) / 32) = (Real.exp ((p : ℝ) / 1024)) ^ 32 := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hp_le : Real.exp ((p : ℝ) / 1024) ≤ 1024 / (1024 - (p : ℝ)) := by
    have hlt : (p : ℝ) / 1024 < 1 := by linarith
    calc Real.exp ((p : ℝ) / 1024) ≤ 1 / (1 - (p : ℝ) / 1024) := exp_le_inv_one_sub hlt
      _ = 1024 / (1024 - (p : ℝ)) := by
        have hne : (1024 - (p : ℝ)) ≠ 0 := by linarith
        field_simp
  rw [hp_eq]
  exact mul_le_mul hn (pow_le_pow_left₀ (Real.exp_pos _).le hp_le 32) (by positivity) (by positivity)

private lemma threshold_lower (r : PrintedRow) :
    (if r.logIndex = 0 then (evenBase : ℝ) else (271828 / 100000 : ℝ) ^ r.logIndex) ≤ r.threshold := by
  unfold PrintedRow.threshold
  split_ifs with hk
  · exact le_rfl
  · have h1 : Real.exp (r.logIndex : ℝ) = (Real.exp 1) ^ r.logIndex := by
      rw [← Real.exp_nat_mul]
      simp
    rw [h1]
    exact pow_le_pow_left₀ (by norm_num) exp_one_bounds.1 r.logIndex

private lemma endpoint_budget_master
    (r : PrintedRow)
    (S_low : ℝ) (n_part p : ℕ) (L_up beta_val : ℝ)
    (hS_pos : 0 < S_low)
    (hp : (p : ℝ) < 1024)
    (hK_pos : 0 < (n_part : ℝ) + (p : ℝ) / 32)
    (hu_pos : 0 < (r.uQ : ℝ)) (hu_lt : (r.uQ : ℝ) < 1)
    (hdel_pos : 0 ≤ (r.deltaQ : ℝ))
    (ha0 : 0 ≤ (r.aQ : ℝ) + 1 / 10000)
    (ha1 : (r.aQ : ℝ) + 1 / 10000 ≤ 1 / 2)
    (hbeta_eq : (betaNum r.m : ℝ) / (betaDen r.m : ℝ) = beta_val)
    (hx0_low : S_low ^ 2 * (1 + (r.deltaQ : ℝ)) ≤
      (if r.logIndex = 0 then (evenBase : ℝ) else (271828 / 100000 : ℝ) ^ r.logIndex) * (1 - (r.uQ : ℝ)))
    (hlog_x0 : Real.log r.threshold ≤ L_up)
    (hlog_x0_nonneg : 0 ≤ Real.log r.threshold)
    (hexp_K : (271829 / 100000 : ℝ) ^ n_part * (1024 / (1024 - (p : ℝ))) ^ 32 ≤ S_low ^ 2 * (r.uQ : ℝ))
    (hmain :
      (2.05022 * 10 ^ (-3 : ℤ)) / ((r.uQ : ℝ) * S_low) +
        2 * (1 + (r.deltaQ : ℝ)) * (L_up / ((n_part : ℝ) + (p : ℝ) / 32)) *
          (1 - (P5 r.m (1 - ((r.aQ : ℝ) + 1 / 10000)) - P5 r.m ((r.aQ : ℝ) + 1 / 10000)) / beta_val) +
        1 / (2 * S_low ^ 4) <
      1 + (r.deltaQ : ℝ) / 2 - (lowZeroBudget r.logIndex + highZeroBudget r.logIndex)) :
    (2.05022 * 10 ^ (-3 : ℤ)) * Real.sqrt (rowEndpointX r) +
      tailCoefficient r.deltaQ r.uQ (rowEndpointX r) * tailMass r.m ((r.aQ : ℝ) + 1 / 10000) /
        (∫ t in (0 : ℝ)..1, weight r.m t) + (r.uQ : ℝ) / (2 * rowEndpointX r) <
      (Real.exp r.uQ - 1) * rowEndpointX r *
        (1 + (r.deltaQ : ℝ) / 2 -
          (lowZeroBudget r.logIndex + highZeroBudget r.logIndex)) := by
  set u : ℝ := (r.uQ : ℝ)
  set δ : ℝ := (r.deltaQ : ℝ)
  set a : ℝ := (r.aQ : ℝ) + 1 / 10000
  set X : ℝ := rowEndpointX r
  set K : ℝ := (n_part : ℝ) + (p : ℝ) / 32
  have heu_sub : u ≤ Real.exp u - 1 := by linarith [Real.add_one_le_exp u]
  have heu_sub_pos : 0 < Real.exp u - 1 := lt_of_lt_of_le hu_pos heu_sub
  have heu_up : Real.exp u ≤ 1 / (1 - u) := exp_le_inv_one_sub hu_lt
  have h1mu_pos : 0 < 1 - u := by linarith
  have h1pδ_pos : 0 < 1 + δ := by linarith
  have hX_ge : S_low ^ 2 ≤ X := by
    change S_low ^ 2 ≤ r.threshold / (Real.exp u * (1 + δ))
    have hth := threshold_lower r
    have hbase_nn : 0 ≤ (if r.logIndex = 0 then (evenBase : ℝ) else (271828 / 100000 : ℝ) ^ r.logIndex) := by
      split_ifs <;> positivity
    have h1 : S_low ^ 2 * (Real.exp u * (1 + δ)) ≤ r.threshold := by
      have heu_mul : Real.exp u * (1 - u) ≤ 1 := (le_div_iff₀ h1mu_pos).mp heu_up
      calc S_low ^ 2 * (Real.exp u * (1 + δ))
          = (S_low ^ 2 * (1 + δ)) * Real.exp u := by ring
        _ ≤ ((if r.logIndex = 0 then (evenBase : ℝ) else (271828 / 100000 : ℝ) ^ r.logIndex) * (1 - u)) * Real.exp u :=
            mul_le_mul_of_nonneg_right hx0_low (Real.exp_pos u).le
        _ = (if r.logIndex = 0 then (evenBase : ℝ) else (271828 / 100000 : ℝ) ^ r.logIndex) * (Real.exp u * (1 - u)) := by ring
        _ ≤ (if r.logIndex = 0 then (evenBase : ℝ) else (271828 / 100000 : ℝ) ^ r.logIndex) * 1 :=
            mul_le_mul_of_nonneg_left heu_mul hbase_nn
        _ ≤ r.threshold := by linarith
    exact (le_div_iff₀ (mul_pos (Real.exp_pos u) h1pδ_pos)).mpr h1
  have hX_pos : 0 < X := lt_of_lt_of_le (sq_pos_of_pos hS_pos) hX_ge
  have hunit_pos : 0 < (Real.exp u - 1) * X := mul_pos heu_sub_pos hX_pos
  have hsqrt_le : Real.sqrt X ≤ X / S_low := by
    have hs1 : S_low ≤ Real.sqrt X := by
      rw [← Real.sqrt_sq hS_pos.le]
      exact Real.sqrt_le_sqrt hX_ge
    rw [le_div_iff₀' hS_pos]
    calc S_low * Real.sqrt X ≤ Real.sqrt X * Real.sqrt X :=
          mul_le_mul_of_nonneg_right hs1 (Real.sqrt_nonneg X)
      _ = X := Real.mul_self_sqrt hX_pos.le
  have ht1 : (2.05022 * 10 ^ (-3 : ℤ)) * Real.sqrt X ≤
      ((2.05022 * 10 ^ (-3 : ℤ)) / (u * S_low)) * ((Real.exp u - 1) * X) := by
    have hc1_pos : (0 : ℝ) ≤ 2.05022 * 10 ^ (-3 : ℤ) := by norm_num
    calc (2.05022 * 10 ^ (-3 : ℤ)) * Real.sqrt X
        ≤ (2.05022 * 10 ^ (-3 : ℤ)) * (X / S_low) := mul_le_mul_of_nonneg_left hsqrt_le hc1_pos
      _ = ((2.05022 * 10 ^ (-3 : ℤ)) / (u * S_low)) * (u * X) := by
          field_simp [hu_pos.ne', hS_pos.ne']
      _ ≤ ((2.05022 * 10 ^ (-3 : ℤ)) / (u * S_low)) * ((Real.exp u - 1) * X) := by
          apply mul_le_mul_of_nonneg_left
          · exact mul_le_mul_of_nonneg_right heu_sub hX_pos.le
          · positivity
  have hX_prod : Real.exp u * X * (1 + δ) = r.threshold := by
    change Real.exp u * (r.threshold / (Real.exp u * (1 + δ))) * (1 + δ) = r.threshold
    have hene : Real.exp u ≠ 0 := (Real.exp_pos u).ne'
    have hdne : 1 + δ ≠ 0 := h1pδ_pos.ne'
    field_simp
  have hlog_den : K ≤ Real.log (X * (Real.exp u - 1)) := by
    rw [Real.le_log_iff_exp_le (mul_pos hX_pos heu_sub_pos)]
    calc Real.exp K ≤ (271829 / 100000 : ℝ) ^ n_part * (1024 / (1024 - (p : ℝ))) ^ 32 :=
          exp_dyadic_upper n_part p hp
      _ ≤ S_low ^ 2 * u := hexp_K
      _ ≤ X * (Real.exp u - 1) := mul_le_mul hX_ge heu_sub hu_pos.le hX_pos.le
  have hlog_pos : 0 < Real.log (X * (Real.exp u - 1)) := lt_of_lt_of_le hK_pos hlog_den
  have hlog_div : Real.log (Real.exp u * X * (1 + δ)) / Real.log (X * (Real.exp u - 1)) ≤ L_up / K := by
    rw [hX_prod]
    calc Real.log r.threshold / Real.log (X * (Real.exp u - 1))
        ≤ L_up / Real.log (X * (Real.exp u - 1)) := div_le_div_of_nonneg_right hlog_x0 hlog_pos.le
      _ ≤ L_up / K := div_le_div_of_nonneg_left (le_trans hlog_x0_nonneg hlog_x0) hK_pos hlog_den
  have htc_le : tailCoefficient δ u X ≤ 2 * (1 + δ) * (L_up / K) * ((Real.exp u - 1) * X) := by
    unfold tailCoefficient
    have h1 : 2 * (1 + δ) * (Real.exp u - 1) *
        (Real.log (Real.exp u * X * (1 + δ)) / Real.log (X * (Real.exp u - 1))) * X ≤
        2 * (1 + δ) * (Real.exp u - 1) * (L_up / K) * X := by
      apply mul_le_mul_of_nonneg_right _ hX_pos.le
      apply mul_le_mul_of_nonneg_left hlog_div
      exact mul_nonneg (mul_nonneg (by norm_num) h1pδ_pos.le) heu_sub_pos.le
    linarith [show 2 * (1 + δ) * (Real.exp u - 1) * (L_up / K) * X =
      2 * (1 + δ) * (L_up / K) * ((Real.exp u - 1) * X) by ring]
  have htm_ratio_nn : 0 ≤ tailMass r.m a / (∫ t in (0 : ℝ)..1, weight r.m t) := by
    rw [integral_weight_zero_one]
    exact div_nonneg (tailMass_nonneg r.m ha0 ha1)
      (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  have htm_ratio_le : tailMass r.m a / (∫ t in (0 : ℝ)..1, weight r.m t) ≤
      1 - (P5 r.m (1 - a) - P5 r.m a) / beta_val := by
    rw [← hbeta_eq]
    exact tailMass_div_le r.m ha0 ha1
  have ht2 : tailCoefficient δ u X * tailMass r.m a / (∫ t in (0 : ℝ)..1, weight r.m t) ≤
      (2 * (1 + δ) * (L_up / K) * (1 - (P5 r.m (1 - a) - P5 r.m a) / beta_val)) *
        ((Real.exp u - 1) * X) := by
    rw [mul_div_assoc]
    have hLup_nn : 0 ≤ L_up := le_trans hlog_x0_nonneg hlog_x0
    have hfac_nn : 0 ≤ 2 * (1 + δ) * (L_up / K) * ((Real.exp u - 1) * X) := by positivity
    calc tailCoefficient δ u X * (tailMass r.m a / (∫ t in (0 : ℝ)..1, weight r.m t))
        ≤ (2 * (1 + δ) * (L_up / K) * ((Real.exp u - 1) * X)) *
            (1 - (P5 r.m (1 - a) - P5 r.m a) / beta_val) :=
          mul_le_mul htc_le htm_ratio_le htm_ratio_nn hfac_nn
      _ = (2 * (1 + δ) * (L_up / K) * (1 - (P5 r.m (1 - a) - P5 r.m a) / beta_val)) *
            ((Real.exp u - 1) * X) := by ring
  have ht3 : u / (2 * X) ≤ (1 / (2 * S_low ^ 4)) * ((Real.exp u - 1) * X) := by
    have hX2 : S_low ^ 4 ≤ X ^ 2 := by
      calc S_low ^ 4 = (S_low ^ 2) ^ 2 := by ring
        _ ≤ X ^ 2 := pow_le_pow_left₀ (by positivity) hX_ge 2
    have h1 : u / (2 * X) ≤ u * X / (2 * S_low ^ 4) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      calc u * (2 * S_low ^ 4) = 2 * u * S_low ^ 4 := by ring
        _ ≤ 2 * u * X ^ 2 := mul_le_mul_of_nonneg_left hX2 (by positivity)
        _ = u * X * (2 * X) := by ring
    calc u / (2 * X) ≤ u * X / (2 * S_low ^ 4) := h1
      _ = (1 / (2 * S_low ^ 4)) * (u * X) := by ring
      _ ≤ (1 / (2 * S_low ^ 4)) * ((Real.exp u - 1) * X) := by
          apply mul_le_mul_of_nonneg_left
          · exact mul_le_mul_of_nonneg_right heu_sub hX_pos.le
          · positivity
  have hsum : (2.05022 * 10 ^ (-3 : ℤ)) * Real.sqrt X +
      tailCoefficient δ u X * tailMass r.m a / (∫ t in (0 : ℝ)..1, weight r.m t) +
      u / (2 * X) ≤
      ((2.05022 * 10 ^ (-3 : ℤ)) / (u * S_low) +
        2 * (1 + δ) * (L_up / K) * (1 - (P5 r.m (1 - a) - P5 r.m a) / beta_val) +
        1 / (2 * S_low ^ 4)) * ((Real.exp u - 1) * X) := by
    linarith
  have hlt_rhs : ((2.05022 * 10 ^ (-3 : ℤ)) / (u * S_low) +
        2 * (1 + δ) * (L_up / K) * (1 - (P5 r.m (1 - a) - P5 r.m a) / beta_val) +
        1 / (2 * S_low ^ 4)) * ((Real.exp u - 1) * X) <
      (1 + δ / 2 - (lowZeroBudget r.logIndex + highZeroBudget r.logIndex)) * ((Real.exp u - 1) * X) :=
    mul_lt_mul_of_pos_right hmain hunit_pos
  linarith

theorem solution (r : PrintedRow) (hr : r = ⟨47, 9, 8080, 1996029891, 92, 2836, 227619375⟩) :
    (2.05022 * 10 ^ (-3 : ℤ)) * Real.sqrt (rowEndpointX r) +
      tailCoefficient r.deltaQ r.uQ (rowEndpointX r) * tailMass r.m ((r.aQ : ℝ) + 1 / 10000) /
        (∫ t in (0 : ℝ)..1, weight r.m t) + (r.uQ : ℝ) / (2 * rowEndpointX r) <
      (Real.exp r.uQ - 1) * rowEndpointX r *
        (1 + (r.deltaQ : ℝ) / 2 -
          (lowZeroBudget r.logIndex + highZeroBudget r.logIndex)) := by
  subst hr
  have hbn : betaNum 9 = 185794560 := by decide
  have hbd : betaDen 9 = 654729075 := by decide
  have hc1 : (9 : ℕ).choose 1 = 9 := by decide
  have hc2 : (9 : ℕ).choose 2 = 36 := by decide
  have hc3 : (9 : ℕ).choose 3 = 84 := by decide
  have hc4 : (9 : ℕ).choose 4 = 126 := by decide
  have hc5 : (9 : ℕ).choose 5 = 126 := by decide
  apply endpoint_budget_master _ (16066000000 : ℝ) 26 5 (47 : ℝ)
    (65536 / 230945 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num [PrintedRow.uQ, PrintedRow.deltaQ]
  · norm_num [PrintedRow.uQ, PrintedRow.deltaQ]
  · norm_num [PrintedRow.deltaQ]
  · norm_num [PrintedRow.aQ]
  · norm_num [PrintedRow.aQ]
  · rw [hbn, hbd]; norm_num
  · norm_num [PrintedRow.uQ, PrintedRow.deltaQ, evenBase]
  · simp [PrintedRow.threshold, Real.log_exp]
  · simp [PrintedRow.threshold, Real.log_exp]
  · norm_num [PrintedRow.uQ, PrintedRow.deltaQ]
  · simp only [PrintedRow.uQ, PrintedRow.deltaQ, PrintedRow.aQ, P5, lowZeroBudget, highZeroBudget,
      hc1, hc2, hc3, hc4, hc5]
    norm_num
