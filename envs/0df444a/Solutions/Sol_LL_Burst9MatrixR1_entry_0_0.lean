-- Prove2me | solution 1 for LL_Burst9MatrixR1.entry_0_0
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-24T01:06:52.378292+00:00
-- url     : https://prove2.me/submissions/81ac85df-8239-4bfe-bfc7-7776bdb863ea

import Mathlib
import Definitions.Def_LL_Burst9MatrixR1_Params
import Definitions.Def_LL_Burst9MatrixR1_alpha
import Definitions.Def_LL_Burst9MatrixR1_ind
import Definitions.Def_LL_Burst9MatrixR1_sigma
import Definitions.Def_LL_Burst9MatrixR1_sigma0
import Definitions.Def_LL_Burst9MatrixR1_Xi1
import Definitions.Def_LL_Burst9MatrixR1_Xi2
import Definitions.Def_LL_Burst9MatrixR1_tableParams
import Definitions.Def_LL_Burst9MatrixR1_grid
import Definitions.Def_LL_Burst9MatrixR1_tableSp
import Definitions.Def_LL_Burst9MatrixR1_candidateMatrixQ
import Definitions.Def_LL_Burst9MatrixR1_tableKernel
import Definitions.Def_LL_Burst9MatrixR1_integralMatrix

open Real Set intervalIntegral Filter MeasureTheory
open scoped Topology
open LL_Burst9MatrixR1

namespace W5Cert_R1_entry_0_0
noncomputable section

private lemma mul_bounds_of_bounds {c x a b : ℝ} (hax : a ≤ x) (hxb : x ≤ b) :
    min (c * a) (c * b) ≤ c * x ∧ c * x ≤ max (c * a) (c * b) := by
  rcases le_total 0 c with hc | hc
  · exact ⟨le_trans (min_le_left _ _) (mul_le_mul_of_nonneg_left hax hc),
      le_trans (mul_le_mul_of_nonneg_left hxb hc) (le_max_right _ _)⟩
  · exact ⟨le_trans (min_le_right _ _) (mul_le_mul_of_nonpos_left hxb hc),
      le_trans (mul_le_mul_of_nonpos_left hax hc) (le_max_left _ _)⟩

private lemma abs_pow_mul_pow_le {a b K : ℝ} (m n : ℕ) (hK : 0 ≤ K)
    (ha : |a| ≤ K) (hb : |b| ≤ K) : |a ^ m * b ^ n| ≤ K ^ (m + n) := by
  rw [abs_mul, abs_pow, abs_pow, pow_add]
  have ha0 := abs_nonneg a
  have hb0 := abs_nonneg b
  gcongr

private lemma artanh_bounds4 (y lo hi : ℝ) (hy0 : 0 ≤ y) (hy1 : y < 1)
    (hlo : lo ≤ 2 * (y + y ^ 3 / 3 + y ^ 5 / 5 + y ^ 7 / 7))
    (hhi : 2 * (y + y ^ 3 / 3 + y ^ 5 / 5 + y ^ 7 / 7) + 2 * y ^ 9 / (9 * (1 - y ^ 2)) ≤ hi) :
    lo ≤ Real.log ((1 + y) / (1 - y)) ∧ Real.log ((1 + y) / (1 - y)) ≤ hi := by
  let g : ℝ → ℝ := fun w =>
    Real.log (1 + w) - Real.log (1 - w) - 2 * (w + w ^ 3 / 3 + w ^ 5 / 5 + w ^ 7 / 7)
  let dg : ℝ → ℝ := fun w => 2 * w ^ 8 / (1 - w ^ 2)
  have hy2 : 0 < 1 - y ^ 2 := by nlinarith only [hy0, hy1]
  have hderiv : ∀ w ∈ uIcc 0 y, HasDerivAt g (dg w) w := by
    intro w hw
    rw [uIcc_of_le hy0] at hw
    have hw1 : 0 < 1 + w := by linarith [hw.1]
    have hw2 : 0 < 1 - w := by linarith [hw.2]
    have h1 : HasDerivAt (fun w => Real.log (1 + w)) (1 / (1 + w)) w := by
      simpa using ((hasDerivAt_id w).const_add 1).log hw1.ne'
    have h2 : HasDerivAt (fun w => Real.log (1 - w)) ((-1) / (1 - w)) w := by
      have hid : HasDerivAt (fun w : ℝ => 1 - w) (-1) w := by
        simpa using (hasDerivAt_id w).const_sub 1
      simpa using hid.log hw2.ne'
    have h3 : HasDerivAt (fun w : ℝ => 2 * (w + w ^ 3 / 3 + y * 0 + w ^ 5 / 5 + w ^ 7 / 7))
        (2 * (1 + w ^ 2 + w ^ 4 + w ^ 6)) w := by
      have hp3 : HasDerivAt (fun w : ℝ => w ^ 3 / 3) (w ^ 2) w :=
        ((hasDerivAt_pow 3 w).div_const 3).congr_deriv (by ring)
      have hp5 : HasDerivAt (fun w : ℝ => w ^ 5 / 5) (w ^ 4) w :=
        ((hasDerivAt_pow 5 w).div_const 5).congr_deriv (by ring)
      have hp7 : HasDerivAt (fun w : ℝ => w ^ 7 / 7) (w ^ 6) w :=
        ((hasDerivAt_pow 7 w).div_const 7).congr_deriv (by ring)
      have hz0 : HasDerivAt (fun _ : ℝ => y * 0) 0 w := hasDerivAt_const w _
      simpa using (((((hasDerivAt_id w).add hp3).add hz0).add hp5).add hp7).const_mul 2
    have h3' : HasDerivAt (fun w : ℝ => 2 * (w + w ^ 3 / 3 + w ^ 5 / 5 + w ^ 7 / 7))
        (2 * (1 + w ^ 2 + w ^ 4 + w ^ 6)) w := by simpa using h3
    refine ((h1.sub h2).sub h3').congr_deriv ?_
    dsimp [dg]
    have hne : 1 - w ^ 2 ≠ 0 := by nlinarith only [hw.1, hw.2, hy1]
    field_simp [hw1.ne', hw2.ne', hne]
    ring
  have hd_cont : ContinuousOn dg (uIcc 0 y) := by
    rw [uIcc_of_le hy0]
    intro w hw
    have hne : 1 - w ^ 2 ≠ 0 := by nlinarith only [hw.1, hw.2, hy1]
    exact ContinuousAt.continuousWithinAt (by dsimp [dg]; fun_prop (disch := exact hne))
  have hint_eq : ∫ w in (0 : ℝ)..y, dg w = g y - g 0 :=
    integral_eq_sub_of_hasDerivAt hderiv hd_cont.intervalIntegrable
  have hg0 : g 0 = 0 := by simp [g]
  have hgy : g y = Real.log ((1 + y) / (1 - y)) - 2 * (y + y ^ 3 / 3 + y ^ 5 / 5 + y ^ 7 / 7) := by
    dsimp [g]
    rw [Real.log_div (by linarith) (by linarith)]
  have h_nonneg : 0 ≤ ∫ w in (0 : ℝ)..y, dg w := by
    apply integral_nonneg hy0
    intro w hw
    dsimp [dg]
    have : 0 < 1 - w ^ 2 := by nlinarith only [hw.1, hw.2, hy1]
    positivity
  have h_upper : ∫ w in (0 : ℝ)..y, dg w ≤ 2 * y ^ 9 / (9 * (1 - y ^ 2)) := by
    let ub : ℝ → ℝ := fun w => 2 * w ^ 8 / (1 - y ^ 2)
    have hub_int : IntervalIntegrable ub volume 0 y := Continuous.intervalIntegrable (by fun_prop) _ _
    have hmono : ∫ w in (0 : ℝ)..y, dg w ≤ ∫ w in (0 : ℝ)..y, ub w := by
      apply integral_mono_on hy0 hd_cont.intervalIntegrable hub_int
      intro w hw
      dsimp [dg, ub]
      have hw2 : 1 - y ^ 2 ≤ 1 - w ^ 2 := by nlinarith only [hw.1, hw.2]
      exact div_le_div_of_nonneg_left (by positivity) hy2 hw2
    have hub_eval : ∫ w in (0 : ℝ)..y, ub w = 2 * y ^ 9 / (9 * (1 - y ^ 2)) := by
      have hanti : ∀ w ∈ uIcc 0 y,
          HasDerivAt (fun w : ℝ => 2 * w ^ 9 / (9 * (1 - y ^ 2))) (ub w) w := by
        intro w _
        refine (((hasDerivAt_pow 9 w).const_mul 2).div_const (9 * (1 - y ^ 2))).congr_deriv ?_
        dsimp [ub]
        field_simp [hy2.ne']
      rw [integral_eq_sub_of_hasDerivAt hanti hub_int]
      ring
    linarith
  rw [hg0, sub_zero, hgy] at hint_eq
  constructor <;> linarith

private lemma artanh_bounds3 (y : ℝ) (hy0 : 0 ≤ y) (hy1 : y < 1) :
    2 * (y + y ^ 3 / 3 + y ^ 5 / 5) ≤ Real.log ((1 + y) / (1 - y)) ∧
      Real.log ((1 + y) / (1 - y)) ≤ 2 * (y + y ^ 3 / 3 + y ^ 5 / 5) + 2 * y ^ 7 / (7 * (1 - y ^ 2)) := by
  let g : ℝ → ℝ := fun w =>
    Real.log (1 + w) - Real.log (1 - w) - 2 * (w + w ^ 3 / 3 + w ^ 5 / 5)
  let dg : ℝ → ℝ := fun w => 2 * w ^ 6 / (1 - w ^ 2)
  have hy2 : 0 < 1 - y ^ 2 := by nlinarith only [hy0, hy1]
  have hderiv : ∀ w ∈ uIcc 0 y, HasDerivAt g (dg w) w := by
    intro w hw
    rw [uIcc_of_le hy0] at hw
    have hw1 : 0 < 1 + w := by linarith [hw.1]
    have hw2 : 0 < 1 - w := by linarith [hw.2]
    have h1 : HasDerivAt (fun w => Real.log (1 + w)) (1 / (1 + w)) w := by
      simpa using ((hasDerivAt_id w).const_add 1).log hw1.ne'
    have h2 : HasDerivAt (fun w => Real.log (1 - w)) ((-1) / (1 - w)) w := by
      have hid : HasDerivAt (fun w : ℝ => 1 - w) (-1) w := by
        simpa using (hasDerivAt_id w).const_sub 1
      simpa using hid.log hw2.ne'
    have h3 : HasDerivAt (fun w : ℝ => 2 * (w + w ^ 3 / 3 + w ^ 5 / 5))
        (2 * (1 + w ^ 2 + w ^ 4)) w := by
      have hp3 : HasDerivAt (fun w : ℝ => w ^ 3 / 3) (w ^ 2) w :=
        ((hasDerivAt_pow 3 w).div_const 3).congr_deriv (by ring)
      have hp5 : HasDerivAt (fun w : ℝ => w ^ 5 / 5) (w ^ 4) w :=
        ((hasDerivAt_pow 5 w).div_const 5).congr_deriv (by ring)
      simpa using (((hasDerivAt_id w).add hp3 |>.add hp5).const_mul 2)
    refine ((h1.sub h2).sub h3).congr_deriv ?_
    dsimp [dg]
    have hne : 1 - w ^ 2 ≠ 0 := by nlinarith only [hw.1, hw.2, hy1]
    field_simp [hw1.ne', hw2.ne', hne]
    ring
  have hd_cont : ContinuousOn dg (uIcc 0 y) := by
    rw [uIcc_of_le hy0]
    intro w hw
    have hne : 1 - w ^ 2 ≠ 0 := by nlinarith only [hw.1, hw.2, hy1]
    exact ContinuousAt.continuousWithinAt (by dsimp [dg]; fun_prop (disch := exact hne))
  have hint_eq : ∫ w in (0 : ℝ)..y, dg w = g y - g 0 :=
    integral_eq_sub_of_hasDerivAt hderiv hd_cont.intervalIntegrable
  have hg0 : g 0 = 0 := by simp [g]
  have hgy : g y = Real.log ((1 + y) / (1 - y)) - 2 * (y + y ^ 3 / 3 + y ^ 5 / 5) := by
    dsimp [g]
    rw [Real.log_div (by linarith) (by linarith)]
  have h_nonneg : 0 ≤ ∫ w in (0 : ℝ)..y, dg w := by
    apply integral_nonneg hy0
    intro w hw
    dsimp [dg]
    have : 0 < 1 - w ^ 2 := by nlinarith only [hw.1, hw.2, hy1]
    positivity
  have h_upper : ∫ w in (0 : ℝ)..y, dg w ≤ 2 * y ^ 7 / (7 * (1 - y ^ 2)) := by
    let ub : ℝ → ℝ := fun w => 2 * w ^ 6 / (1 - y ^ 2)
    have hub_int : IntervalIntegrable ub volume 0 y := Continuous.intervalIntegrable (by fun_prop) _ _
    have hmono : ∫ w in (0 : ℝ)..y, dg w ≤ ∫ w in (0 : ℝ)..y, ub w := by
      apply integral_mono_on hy0 hd_cont.intervalIntegrable hub_int
      intro w hw
      dsimp [dg, ub]
      have hw2 : 1 - y ^ 2 ≤ 1 - w ^ 2 := by nlinarith only [hw.1, hw.2]
      exact div_le_div_of_nonneg_left (by positivity) hy2 hw2
    have hub_eval : ∫ w in (0 : ℝ)..y, ub w = 2 * y ^ 7 / (7 * (1 - y ^ 2)) := by
      have hanti : ∀ w ∈ uIcc 0 y,
          HasDerivAt (fun w : ℝ => 2 * w ^ 7 / (7 * (1 - y ^ 2))) (ub w) w := by
        intro w _
        refine (((hasDerivAt_pow 7 w).const_mul 2).div_const (7 * (1 - y ^ 2))).congr_deriv ?_
        dsimp [ub]
        field_simp [hy2.ne']
      rw [integral_eq_sub_of_hasDerivAt hanti hub_int]
      ring
    linarith
  rw [hg0, sub_zero, hgy] at hint_eq
  constructor <;> linarith

def LOG2_LO : ℝ := 173286795139971 / 250000000000000
def LOG2_HI : ℝ := 346573590279973 / 500000000000000
def LOG3_LO : ℝ := 549306144334007 / 500000000000000
def LOG3_HI : ℝ := 1098612288668111 / 1000000000000000
def LOG5_LO : ℝ := 1609437912433961 / 1000000000000000
def LOG5_HI : ℝ := 804718956217051 / 500000000000000

private lemma base_logs :
    (LOG2_LO ≤ Real.log 2 ∧ Real.log 2 ≤ LOG2_HI) ∧
    (LOG3_LO ≤ Real.log 3 ∧ Real.log 3 ≤ LOG3_HI) ∧
    (LOG5_LO ≤ Real.log 5 ∧ Real.log 5 ≤ LOG5_HI) := by
  obtain ⟨ha1, ha2⟩ := artanh_bounds4 (1 / 31)
    (645385211375627 / 10000000000000000) (20168287855491 / 312500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨hb1, hb2⟩ := artanh_bounds4 (1 / 49)
    (408219945202549 / 10000000000000000) (51027493150319 / 1250000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨hc1, hc2⟩ := artanh_bounds4 (1 / 161)
    (124225199985571 / 10000000000000000) (31056299996393 / 2500000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have ha_eq : Real.log ((1 + (1 / 31 : ℝ)) / (1 - 1 / 31)) =
      4 * Real.log 2 - Real.log 3 - Real.log 5 := by
    have : (1 + (1 / 31 : ℝ)) / (1 - 1 / 31) = (2 : ℝ) ^ (4 : ℕ) / (3 * 5) := by norm_num
    rw [this, Real.log_div (by positivity) (by positivity),
      Real.log_pow, Real.log_mul (by positivity) (by positivity)]
    ring
  have hb_eq : Real.log ((1 + (1 / 49 : ℝ)) / (1 - 1 / 49)) =
      2 * Real.log 5 - 3 * Real.log 2 - Real.log 3 := by
    have : (1 + (1 / 49 : ℝ)) / (1 - 1 / 49) = (5 : ℝ) ^ (2 : ℕ) / ((2 : ℝ) ^ (3 : ℕ) * 3) := by norm_num
    rw [this, Real.log_div (by positivity) (by positivity),
      Real.log_pow, Real.log_mul (by positivity) (by positivity), Real.log_pow]
    ring
  have hc_eq : Real.log ((1 + (1 / 161 : ℝ)) / (1 - 1 / 161)) =
      4 * Real.log 3 - 4 * Real.log 2 - Real.log 5 := by
    have : (1 + (1 / 161 : ℝ)) / (1 - 1 / 161) = (3 : ℝ) ^ (4 : ℕ) / ((2 : ℝ) ^ (4 : ℕ) * 5) := by norm_num
    rw [this, Real.log_div (by positivity) (by positivity),
      Real.log_pow, Real.log_mul (by positivity) (by positivity), Real.log_pow]
    ring
  rw [ha_eq] at ha1 ha2
  rw [hb_eq] at hb1 hb2
  rw [hc_eq] at hc1 hc2
  dsimp [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI]
  refine ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩

private lemma log_rat_bounds (M y : ℝ) (e2 e3 e5 : ℤ) (lo hi : ℝ)
    (hy0 : 0 ≤ y) (hy1 : y < 1)
    (hM : M * (1 - y) = (2 : ℝ) ^ e2 * (3 : ℝ) ^ e3 * (5 : ℝ) ^ e5 * (1 + y))
    (hlo : lo ≤ min (e2 * LOG2_LO) (e2 * LOG2_HI) + min (e3 * LOG3_LO) (e3 * LOG3_HI) +
        min (e5 * LOG5_LO) (e5 * LOG5_HI) + 2 * (y + y ^ 3 / 3 + y ^ 5 / 5))
    (hhi : max (e2 * LOG2_LO) (e2 * LOG2_HI) + max (e3 * LOG3_LO) (e3 * LOG3_HI) +
        max (e5 * LOG5_LO) (e5 * LOG5_HI) +
        2 * (y + y ^ 3 / 3 + y ^ 5 / 5) + 2 * y ^ 7 / (7 * (1 - y ^ 2)) ≤ hi) :
    lo ≤ Real.log M ∧ Real.log M ≤ hi := by
  obtain ⟨⟨h2l, h2h⟩, ⟨h3l, h3h⟩, ⟨h5l, h5h⟩⟩ := base_logs
  obtain ⟨hb2l, hb2h⟩ := mul_bounds_of_bounds (c := (e2 : ℝ)) h2l h2h
  obtain ⟨hb3l, hb3h⟩ := mul_bounds_of_bounds (c := (e3 : ℝ)) h3l h3h
  obtain ⟨hb5l, hb5h⟩ := mul_bounds_of_bounds (c := (e5 : ℝ)) h5l h5h
  obtain ⟨hart1, hart2⟩ := artanh_bounds3 y hy0 hy1
  have hG_pos : (0 : ℝ) < (2 : ℝ) ^ e2 * (3 : ℝ) ^ e3 * (5 : ℝ) ^ e5 := by positivity
  have h1my : (0 : ℝ) < 1 - y := by linarith
  have h1py : (0 : ℝ) < 1 + y := by linarith
  have hM_eq : M = (2 : ℝ) ^ e2 * (3 : ℝ) ^ e3 * (5 : ℝ) ^ e5 * ((1 + y) / (1 - y)) := by
    calc M = M * (1 - y) / (1 - y) := (mul_div_cancel_right₀ M h1my.ne').symm
      _ = (2 : ℝ) ^ e2 * (3 : ℝ) ^ e3 * (5 : ℝ) ^ e5 * (1 + y) / (1 - y) := by rw [hM]
      _ = (2 : ℝ) ^ e2 * (3 : ℝ) ^ e3 * (5 : ℝ) ^ e5 * ((1 + y) / (1 - y)) := mul_div_assoc _ _ _
  have hlogM : Real.log M = e2 * Real.log 2 + e3 * Real.log 3 + e5 * Real.log 5 +
      Real.log ((1 + y) / (1 - y)) := by
    rw [hM_eq, Real.log_mul hG_pos.ne' (div_pos h1py h1my).ne',
      Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity),
      Real.log_zpow, Real.log_zpow, Real.log_zpow]
  rw [hlogM]
  constructor <;> linarith

private lemma abs_log_one_add_sub_P5 (z : ℝ) (hz : |z| ≤ 1 / 10) :
    |Real.log (1 + z) - (z - z ^ 2 / 2 + z ^ 3 / 3 - z ^ 4 / 4 + z ^ 5 / 5)| ≤ 5 / 27 * z ^ 6 := by
  have hz_bounds := abs_le.mp hz
  let g : ℝ → ℝ := fun w => Real.log (1 + w) - (w - w ^ 2 / 2 + w ^ 3 / 3 - w ^ 4 / 4 + w ^ 5 / 5)
  let dg : ℝ → ℝ := fun w => -(w ^ 5) / (1 + w)
  have hderiv : ∀ w, -1 / 10 ≤ w → w ≤ 1 / 10 → HasDerivAt g (dg w) w := by
    intro w hw1 _
    have hpos : 0 < 1 + w := by linarith
    have h1 : HasDerivAt (fun w => Real.log (1 + w)) (1 / (1 + w)) w := by
      simpa using ((hasDerivAt_id w).const_add 1).log hpos.ne'
    have hp2 : HasDerivAt (fun w : ℝ => w ^ 2 / 2) w w :=
      ((hasDerivAt_pow 2 w).div_const 2).congr_deriv (by ring)
    have hp3 : HasDerivAt (fun w : ℝ => w ^ 3 / 3) (w ^ 2) w :=
      ((hasDerivAt_pow 3 w).div_const 3).congr_deriv (by ring)
    have hp4 : HasDerivAt (fun w : ℝ => w ^ 4 / 4) (w ^ 3) w :=
      ((hasDerivAt_pow 4 w).div_const 4).congr_deriv (by ring)
    have hp5 : HasDerivAt (fun w : ℝ => w ^ 5 / 5) (w ^ 4) w :=
      ((hasDerivAt_pow 5 w).div_const 5).congr_deriv (by ring)
    have hpoly := (((hasDerivAt_id w).sub hp2).add hp3 |>.sub hp4).add hp5
    refine (h1.sub hpoly).congr_deriv ?_
    dsimp [dg]
    field_simp [hpos.ne']
    ring
  rcases le_total 0 z with hz0 | hz0
  · have hd_cont : ContinuousOn dg (uIcc 0 z) := by
      rw [uIcc_of_le hz0]
      intro w hw
      have hne : 1 + w ≠ 0 := by linarith [hw.1]
      exact ContinuousAt.continuousWithinAt (by dsimp [dg]; fun_prop (disch := exact hne))
    have hint : ∫ w in (0 : ℝ)..z, dg w = g z - g 0 := by
      apply integral_eq_sub_of_hasDerivAt _ hd_cont.intervalIntegrable
      intro w hw
      rw [uIcc_of_le hz0] at hw
      exact hderiv w (by linarith [hw.1]) (by linarith [hw.2, hz_bounds.2])
    have hg0 : g 0 = 0 := by simp [g]
    have h_le0 : ∫ w in (0 : ℝ)..z, dg w ≤ 0 := by
      rw [← neg_nonneg, ← intervalIntegral.integral_neg]
      apply integral_nonneg hz0
      intro w hw
      dsimp [dg]
      have : 0 < 1 + w := by linarith [hw.1]
      have : 0 ≤ w ^ 5 := pow_nonneg hw.1 5
      rw [neg_div, neg_neg]
      positivity
    have h_lb : -(5 / 27 * z ^ 6) ≤ ∫ w in (0 : ℝ)..z, dg w := by
      let lb : ℝ → ℝ := fun w => -(10 / 9) * w ^ 5
      have hlb_int : IntervalIntegrable lb volume 0 z := Continuous.intervalIntegrable (by fun_prop) _ _
      have hmono : ∫ w in (0 : ℝ)..z, lb w ≤ ∫ w in (0 : ℝ)..z, dg w := by
        apply integral_mono_on hz0 hlb_int hd_cont.intervalIntegrable
        intro w hw
        dsimp [lb, dg]
        have hw1 : (9 / 10 : ℝ) ≤ 1 + w := by linarith [hw.1]
        have hw5 : 0 ≤ w ^ 5 := pow_nonneg hw.1 5
        have hdiv : w ^ 5 / (1 + w) ≤ w ^ 5 / (9 / 10) :=
          div_le_div_of_nonneg_left hw5 (by norm_num) hw1
        rw [neg_div]
        linarith
      have hlb_eval : ∫ w in (0 : ℝ)..z, lb w = -(5 / 27 * z ^ 6) := by
        have hanti : ∀ w ∈ uIcc 0 z, HasDerivAt (fun w : ℝ => -(5 / 27) * w ^ 6) (lb w) w := by
          intro w _
          refine ((hasDerivAt_pow 6 w).const_mul (-(5 / 27 : ℝ))).congr_deriv ?_
          dsimp [lb]; ring
        rw [integral_eq_sub_of_hasDerivAt hanti hlb_int]
        ring
      linarith
    rw [hg0, sub_zero] at hint
    dsimp [g] at hint
    rw [abs_le]
    have : 0 ≤ z ^ 6 := by positivity
    constructor <;> linarith
  · have hd_cont : ContinuousOn dg (uIcc z 0) := by
      rw [uIcc_of_le hz0]
      intro w hw
      have hne : 1 + w ≠ 0 := by linarith [hw.1, hz_bounds.1]
      exact ContinuousAt.continuousWithinAt (by dsimp [dg]; fun_prop (disch := exact hne))
    have hint : ∫ w in z..(0 : ℝ), dg w = g 0 - g z := by
      apply integral_eq_sub_of_hasDerivAt _ hd_cont.intervalIntegrable
      intro w hw
      rw [uIcc_of_le hz0] at hw
      exact hderiv w (by linarith [hw.1, hz_bounds.1]) (by linarith [hw.2])
    have hg0 : g 0 = 0 := by simp [g]
    have h_ge0 : 0 ≤ ∫ w in z..(0 : ℝ), dg w := by
      apply integral_nonneg hz0
      intro w hw
      dsimp [dg]
      have hpos : 0 < 1 + w := by linarith [hw.1, hz_bounds.1]
      have hw5 : 0 ≤ -w ^ 5 := by
        have hnw : 0 ≤ (-w) ^ 5 := pow_nonneg (by linarith [hw.2]) 5
        have : (-w) ^ 5 = -w ^ 5 := by ring
        linarith
      exact div_nonneg hw5 hpos.le
    have h_ub : ∫ w in z..(0 : ℝ), dg w ≤ 5 / 27 * z ^ 6 := by
      let ub : ℝ → ℝ := fun w => -(10 / 9) * w ^ 5
      have hub_int : IntervalIntegrable ub volume z 0 := Continuous.intervalIntegrable (by fun_prop) _ _
      have hmono : ∫ w in z..(0 : ℝ), dg w ≤ ∫ w in z..(0 : ℝ), ub w := by
        apply integral_mono_on hz0 hd_cont.intervalIntegrable hub_int
        intro w hw
        dsimp [ub, dg]
        have hw1 : (9 / 10 : ℝ) ≤ 1 + w := by linarith [hw.1, hz_bounds.1]
        have hw5 : 0 ≤ -w ^ 5 := by
          have hnw : 0 ≤ (-w) ^ 5 := pow_nonneg (by linarith [hw.2]) 5
          have : (-w) ^ 5 = -w ^ 5 := by ring
          linarith
        have hdiv : (-w ^ 5) / (1 + w) ≤ (-w ^ 5) / (9 / 10) :=
          div_le_div_of_nonneg_left hw5 (by norm_num) hw1
        linarith
      have hub_eval : ∫ w in z..(0 : ℝ), ub w = 5 / 27 * z ^ 6 := by
        have hanti : ∀ w ∈ uIcc z 0, HasDerivAt (fun w : ℝ => -(5 / 27) * w ^ 6) (ub w) w := by
          intro w _
          refine ((hasDerivAt_pow 6 w).const_mul (-(5 / 27 : ℝ))).congr_deriv ?_
          dsimp [ub]; ring
        rw [integral_eq_sub_of_hasDerivAt hanti hub_int]
        ring
      linarith
    rw [hg0, zero_sub] at hint
    dsimp [g] at hint
    rw [abs_le]
    have : 0 ≤ z ^ 6 := by positivity
    constructor <;> linarith

private lemma abs_log_one_add_sub_P3 (z : ℝ) (hz : |z| ≤ 1 / 10) :
    |Real.log (1 + z) - (z - z ^ 2 / 2 + z ^ 3 / 3)| ≤ 5 / 18 * z ^ 4 := by
  have hp5 := abs_log_one_add_sub_P5 z hz
  have hzb := abs_le.mp hz
  have hz2 : z ^ 2 ≤ 1 / 100 := by nlinarith only [hzb.1, hzb.2]
  have hz4 : 0 ≤ z ^ 4 := by positivity
  have hz6 : z ^ 6 ≤ z ^ 4 / 100 := by
    have : z ^ 6 = z ^ 4 * z ^ 2 := by ring
    nlinarith only [this, hz2, hz4]
  have htail : |-z ^ 4 / 4 + z ^ 5 / 5| ≤ 5 / 18 * z ^ 4 - 5 / 27 * z ^ 6 := by
    rw [abs_le]
    have hz5 : |z ^ 5| ≤ z ^ 4 / 10 := by
      have : |z ^ 5| = z ^ 4 * |z| := by
        rw [abs_pow, show (5 : ℕ) = 4 + 1 from rfl, pow_add, pow_one]
        have : |z| ^ 4 = z ^ 4 := by rw [← abs_pow, abs_of_nonneg hz4]
        rw [this]
      nlinarith only [this, hz, hz4]
    have hz5b := abs_le.mp hz5
    constructor <;> linarith
  have htri : |Real.log (1 + z) - (z - z ^ 2 / 2 + z ^ 3 / 3)| ≤
      |Real.log (1 + z) - (z - z ^ 2 / 2 + z ^ 3 / 3 - z ^ 4 / 4 + z ^ 5 / 5)| +
        |-z ^ 4 / 4 + z ^ 5 / 5| := by
    have hid : Real.log (1 + z) - (z - z ^ 2 / 2 + z ^ 3 / 3) =
        (Real.log (1 + z) - (z - z ^ 2 / 2 + z ^ 3 / 3 - z ^ 4 / 4 + z ^ 5 / 5)) +
          (-z ^ 4 / 4 + z ^ 5 / 5) := by ring
    rw [hid]
    exact abs_add_le _ _
  linarith

private lemma integral_centered_poly6 (c0 c1 c2 c3 c4 c5 c6 u v m h : ℝ)
    (hm : m = (u + v) / 2) (hh : h = (v - u) / 2) :
    ∫ t in u..v, (c0 + c1 * (t - m) + c2 * (t - m) ^ 2 +
        c3 * (t - m) ^ 3 + c4 * (t - m) ^ 4 +
        c5 * (t - m) ^ 5 + c6 * (t - m) ^ 6) =
      2 * h * c0 + 2 / 3 * h ^ 3 * c2 + 2 / 5 * h ^ 5 * c4 + 2 / 7 * h ^ 7 * c6 := by
  let anti : ℝ → ℝ := fun t =>
    c0 * (t - m) + c1 / 2 * (t - m) ^ 2 + c2 / 3 * (t - m) ^ 3 +
      c3 / 4 * (t - m) ^ 4 + c4 / 5 * (t - m) ^ 5 + c5 / 6 * (t - m) ^ 6 + c6 / 7 * (t - m) ^ 7
  let integrand : ℝ → ℝ := fun t =>
    c0 + c1 * (t - m) + c2 * (t - m) ^ 2 + c3 * (t - m) ^ 3 +
      c4 * (t - m) ^ 4 + c5 * (t - m) ^ 5 + c6 * (t - m) ^ 6
  have hderiv : ∀ t ∈ uIcc u v, HasDerivAt anti (integrand t) t := by
    intro t _
    have hs : HasDerivAt (fun t : ℝ => t - m) 1 t := by
      simpa using (hasDerivAt_id t).sub_const m
    have d1 := hs.const_mul c0
    have d2 := (hs.pow 2).const_mul (c1 / 2)
    have d3 := (hs.pow 3).const_mul (c2 / 3)
    have d4 := (hs.pow 4).const_mul (c3 / 4)
    have d5 := (hs.pow 5).const_mul (c4 / 5)
    have d6 := (hs.pow 6).const_mul (c5 / 6)
    have d7 := (hs.pow 7).const_mul (c6 / 7)
    refine ((((((d1.add d2).add d3).add d4).add d5).add d6).add d7).congr_deriv ?_
    dsimp [integrand]
    ring
  have hint : IntervalIntegrable integrand volume u v :=
    Continuous.intervalIntegrable (by fun_prop) _ _
  rw [integral_eq_sub_of_hasDerivAt hderiv hint]
  dsimp [anti]
  rw [hm, hh]
  ring

def quadLogLo (h b d K L_lo N : ℝ) : ℝ :=
  (min (L_lo * (2 * h * (1 + d ^ 2 * h ^ 2 / 3 + d ^ 4 * h ^ 4 / 5)))
       (L_lo * (2 * h * (1 + d ^ 2 * h ^ 2 / 3 + d ^ 4 * h ^ 4 / 5) + 20 / 63 * d ^ 6 * h ^ 7)) +
   (-2 / 3 * h ^ 3 * (b ^ 2 / 2 + b * d) -
    2 / 5 * h ^ 5 * (b ^ 4 / 4 + b ^ 3 * d / 3 + b ^ 2 * d ^ 2 / 2 + b * d ^ 3) -
    K ^ 6 * h ^ 7)) / N

def quadLogHi (h b d K L_hi N : ℝ) : ℝ :=
  (max (L_hi * (2 * h * (1 + d ^ 2 * h ^ 2 / 3 + d ^ 4 * h ^ 4 / 5)))
       (L_hi * (2 * h * (1 + d ^ 2 * h ^ 2 / 3 + d ^ 4 * h ^ 4 / 5) + 20 / 63 * d ^ 6 * h ^ 7)) +
   (-2 / 3 * h ^ 3 * (b ^ 2 / 2 + b * d) -
    2 / 5 * h ^ 5 * (b ^ 4 / 4 + b ^ 3 * d / 3 + b ^ 2 * d ^ 2 / 2 + b * d ^ 3) +
    K ^ 6 * h ^ 7)) / N

private lemma quad_log_div_sub (A B C D u v m h M N b d K L_lo L_hi out_lo out_hi : ℝ)
    (huv : u ≤ v)
    (hm : m = (u + v) / 2) (hh : h = (v - u) / 2)
    (hM_eq : M = A + B * m) (hN_eq : N = C + D * m)
    (hb_eq : B = M * b) (hd_eq : D = N * d)
    (hM : 0 < M) (hN : 0 < N) (hK0 : 0 ≤ K)
    (hb_le : |b| ≤ K) (hd_le : |d| ≤ K) (hKh : K * h ≤ 1 / 10)
    (hL : L_lo ≤ Real.log M ∧ Real.log M ≤ L_hi)
    (hout_lo : out_lo ≤ quadLogLo h b d K L_lo N)
    (hout_hi : quadLogHi h b d K L_hi N ≤ out_hi) :
    IntervalIntegrable (fun t => Real.log (A + B * t) / (C + D * t)) volume u v ∧
      out_lo ≤ ∫ t in u..v, Real.log (A + B * t) / (C + D * t) ∧
      ∫ t in u..v, Real.log (A + B * t) / (C + D * t) ≤ out_hi := by
  have hh0 : 0 ≤ h := by linarith
  have hAt_id : ∀ t : ℝ, A + B * t = M * (1 + b * (t - m)) := fun t => by
    calc A + B * t = (A + B * m) + B * (t - m) := by ring
      _ = M + (M * b) * (t - m) := by rw [← hM_eq, hb_eq]
      _ = M * (1 + b * (t - m)) := by ring
  have hCt_id : ∀ t : ℝ, C + D * t = N * (1 + d * (t - m)) := fun t => by
    calc C + D * t = (C + D * m) + D * (t - m) := by ring
      _ = N + (N * d) * (t - m) := by rw [← hN_eq, hd_eq]
      _ = N * (1 + d * (t - m)) := by ring
  have h_pt : ∀ t ∈ Icc u v, |t - m| ≤ h ∧ |b * (t - m)| ≤ 1 / 10 ∧ |d * (t - m)| ≤ 1 / 10 ∧
      9 / 10 ≤ 1 + b * (t - m) ∧ 9 / 10 ≤ 1 + d * (t - m) := by
    intro t ht
    have htm : |t - m| ≤ h := by
      rw [abs_le]; constructor <;> linarith [ht.1, ht.2]
    have hbx : |b * (t - m)| ≤ 1 / 10 := by
      rw [abs_mul]
      calc |b| * |t - m| ≤ K * h := mul_le_mul hb_le htm (abs_nonneg _) hK0
        _ ≤ 1 / 10 := hKh
    have hdx : |d * (t - m)| ≤ 1 / 10 := by
      rw [abs_mul]
      calc |d| * |t - m| ≤ K * h := mul_le_mul hd_le htm (abs_nonneg _) hK0
        _ ≤ 1 / 10 := hKh
    exact ⟨htm, hbx, hdx, by linarith [(abs_le.mp hbx).1], by linarith [(abs_le.mp hdx).1]⟩
  have hf_cont : ContinuousOn (fun t => Real.log (A + B * t) / (C + D * t)) (Icc u v) := by
    intro t ht
    obtain ⟨_, _, _, hb1, hd1⟩ := h_pt t ht
    have hA_ne : A + B * t ≠ 0 := by rw [hAt_id t]; positivity
    have hC_ne : C + D * t ≠ 0 := by rw [hCt_id t]; positivity
    exact ContinuousAt.continuousWithinAt (by fun_prop (disch := assumption))
  have hf_int : IntervalIntegrable (fun t => Real.log (A + B * t) / (C + D * t)) volume u v :=
    hf_cont.intervalIntegrable_of_Icc huv
  let g1 : ℝ → ℝ := fun t => 1 / (1 + d * (t - m))
  let g2 : ℝ → ℝ := fun t => Real.log (1 + b * (t - m)) / (1 + d * (t - m))
  have hg1_int : IntervalIntegrable g1 volume u v := by
    apply ContinuousOn.intervalIntegrable_of_Icc huv
    intro t ht
    have hne : 1 + d * (t - m) ≠ 0 := by linarith [(h_pt t ht).2.2.2.2]
    exact ContinuousAt.continuousWithinAt (by dsimp [g1]; fun_prop (disch := exact hne))
  have hg2_int : IntervalIntegrable g2 volume u v := by
    apply ContinuousOn.intervalIntegrable_of_Icc huv
    intro t ht
    have hne1 : 1 + b * (t - m) ≠ 0 := by linarith [(h_pt t ht).2.2.2.1]
    have hne2 : 1 + d * (t - m) ≠ 0 := by linarith [(h_pt t ht).2.2.2.2]
    exact ContinuousAt.continuousWithinAt (by dsimp [g2]; fun_prop (disch := assumption))
  have hsplit_eq : ∫ t in u..v, Real.log (A + B * t) / (C + D * t) =
      ((Real.log M * ∫ t in u..v, g1 t) + ∫ t in u..v, g2 t) / N := by
    have hcongr : EqOn (fun t => Real.log (A + B * t) / (C + D * t))
        (fun t => (Real.log M / N) * g1 t + (1 / N) * g2 t) (uIcc u v) := by
      rw [uIcc_of_le huv]
      intro t ht
      dsimp only
      obtain ⟨_, _, _, hb1, hd1⟩ := h_pt t ht
      rw [hAt_id t, hCt_id t, Real.log_mul hM.ne' (by linarith)]
      dsimp [g1, g2]
      have hd_ne : 1 + d * (t - m) ≠ 0 := by linarith
      field_simp [hN.ne', hd_ne]
    calc ∫ t in u..v, Real.log (A + B * t) / (C + D * t)
        = ∫ t in u..v, ((Real.log M / N) * g1 t + (1 / N) * g2 t) := integral_congr hcongr
      _ = (∫ t in u..v, (Real.log M / N) * g1 t) + ∫ t in u..v, (1 / N) * g2 t :=
          integral_add (hg1_int.const_mul _) (hg2_int.const_mul _)
      _ = (Real.log M / N) * (∫ t in u..v, g1 t) + (1 / N) * ∫ t in u..v, g2 t := by
          rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
      _ = ((Real.log M * ∫ t in u..v, g1 t) + ∫ t in u..v, g2 t) / N := by ring
  let q_lo_fn : ℝ → ℝ := fun t =>
    1 + (-d) * (t - m) + d ^ 2 * (t - m) ^ 2 + (-d ^ 3) * (t - m) ^ 3 +
      d ^ 4 * (t - m) ^ 4 + (-d ^ 5) * (t - m) ^ 5 + 0 * (t - m) ^ 6
  let q_hi_fn : ℝ → ℝ := fun t =>
    1 + (-d) * (t - m) + d ^ 2 * (t - m) ^ 2 + (-d ^ 3) * (t - m) ^ 3 +
      d ^ 4 * (t - m) ^ 4 + (-d ^ 5) * (t - m) ^ 5 + (10 / 9 * d ^ 6) * (t - m) ^ 6
  have hg1_lo : 2 * h * (1 + d ^ 2 * h ^ 2 / 3 + d ^ 4 * h ^ 4 / 5) ≤ ∫ t in u..v, g1 t := by
    have hm1 : ∫ t in u..v, q_lo_fn t ≤ ∫ t in u..v, g1 t := by
      apply integral_mono_on huv (Continuous.intervalIntegrable (by fun_prop) _ _) hg1_int
      intro t ht
      obtain ⟨_, _, _, _, hd1⟩ := h_pt t ht
      dsimp [q_lo_fn, g1]
      have hpos : 0 < 1 + d * (t - m) := by linarith
      rw [le_div_iff₀ hpos]
      have hid : (1 + (-d) * (t - m) + d ^ 2 * (t - m) ^ 2 + (-d ^ 3) * (t - m) ^ 3 +
          d ^ 4 * (t - m) ^ 4 + (-d ^ 5) * (t - m) ^ 5 + 0 * (t - m) ^ 6) * (1 + d * (t - m)) =
          1 - d ^ 6 * (t - m) ^ 6 := by ring
      have h6 : 0 ≤ d ^ 6 * (t - m) ^ 6 := by positivity
      linarith
    have hev := integral_centered_poly6 1 (-d) (d ^ 2) (-d ^ 3) (d ^ 4) (-d ^ 5) 0 u v m h hm hh
    dsimp [q_lo_fn] at hm1
    linarith
  have hg1_hi : ∫ t in u..v, g1 t ≤
      2 * h * (1 + d ^ 2 * h ^ 2 / 3 + d ^ 4 * h ^ 4 / 5) + 20 / 63 * d ^ 6 * h ^ 7 := by
    have hm1 : ∫ t in u..v, g1 t ≤ ∫ t in u..v, q_hi_fn t := by
      apply integral_mono_on huv hg1_int (Continuous.intervalIntegrable (by fun_prop) _ _)
      intro t ht
      obtain ⟨_, _, _, _, hd1⟩ := h_pt t ht
      dsimp [q_hi_fn, g1]
      have hpos : 0 < 1 + d * (t - m) := by linarith
      rw [div_le_iff₀ hpos]
      have hid : 1 - (1 + (-d) * (t - m) + d ^ 2 * (t - m) ^ 2 + (-d ^ 3) * (t - m) ^ 3 +
          d ^ 4 * (t - m) ^ 4 + (-d ^ 5) * (t - m) ^ 5) * (1 + d * (t - m)) =
          d ^ 6 * (t - m) ^ 6 := by ring
      have h6 : 0 ≤ d ^ 6 * (t - m) ^ 6 := by positivity
      nlinarith only [hd1, hid, h6]
    have hev := integral_centered_poly6 1 (-d) (d ^ 2) (-d ^ 3) (d ^ 4) (-d ^ 5) (10 / 9 * d ^ 6) u v m h hm hh
    dsimp [q_hi_fn] at hm1
    linarith
  have hIq_pos : 0 ≤ 2 * h * (1 + d ^ 2 * h ^ 2 / 3 + d ^ 4 * h ^ 4 / 5) := by positivity
  have hg1_nonneg : 0 ≤ ∫ t in u..v, g1 t := le_trans hIq_pos hg1_lo
  have hLM_lo : min (L_lo * (2 * h * (1 + d ^ 2 * h ^ 2 / 3 + d ^ 4 * h ^ 4 / 5)))
      (L_lo * (2 * h * (1 + d ^ 2 * h ^ 2 / 3 + d ^ 4 * h ^ 4 / 5) + 20 / 63 * d ^ 6 * h ^ 7)) ≤
      Real.log M * ∫ t in u..v, g1 t := by
    have hb_lo := (mul_bounds_of_bounds (c := L_lo) hg1_lo hg1_hi).1
    have hle : L_lo * ∫ t in u..v, g1 t ≤ Real.log M * ∫ t in u..v, g1 t :=
      mul_le_mul_of_nonneg_right hL.1 hg1_nonneg
    linarith
  have hLM_hi : Real.log M * ∫ t in u..v, g1 t ≤
      max (L_hi * (2 * h * (1 + d ^ 2 * h ^ 2 / 3 + d ^ 4 * h ^ 4 / 5)))
      (L_hi * (2 * h * (1 + d ^ 2 * h ^ 2 / 3 + d ^ 4 * h ^ 4 / 5) + 20 / 63 * d ^ 6 * h ^ 7)) := by
    have hb_hi := (mul_bounds_of_bounds (c := L_hi) hg1_lo hg1_hi).2
    have hle : Real.log M * ∫ t in u..v, g1 t ≤ L_hi * ∫ t in u..v, g1 t :=
      mul_le_mul_of_nonneg_right hL.2 hg1_nonneg
    linarith
  have hg2_bounds :
      (-2 / 3 * h ^ 3 * (b ^ 2 / 2 + b * d) -
       2 / 5 * h ^ 5 * (b ^ 4 / 4 + b ^ 3 * d / 3 + b ^ 2 * d ^ 2 / 2 + b * d ^ 3) -
       K ^ 6 * h ^ 7) ≤ ∫ t in u..v, g2 t ∧
      ∫ t in u..v, g2 t ≤
      (-2 / 3 * h ^ 3 * (b ^ 2 / 2 + b * d) -
       2 / 5 * h ^ 5 * (b ^ 4 / 4 + b ^ 3 * d / 3 + b ^ 2 * d ^ 2 / 2 + b * d ^ 3) +
       K ^ 6 * h ^ 7) := by
    have hrem : |d * (b ^ 5 / 5 + b ^ 4 * d / 4 + b ^ 3 * d ^ 2 / 3 + b ^ 2 * d ^ 3 / 2 + b * d ^ 4)| ≤
        137 / 60 * K ^ 6 := by
      have h51 := abs_pow_mul_pow_le 5 1 hK0 hb_le hd_le
      have h42 := abs_pow_mul_pow_le 4 2 hK0 hb_le hd_le
      have h33 := abs_pow_mul_pow_le 3 3 hK0 hb_le hd_le
      have h24 := abs_pow_mul_pow_le 2 4 hK0 hb_le hd_le
      have h15 := abs_pow_mul_pow_le 1 5 hK0 hb_le hd_le
      change |b ^ 5 * d ^ 1| ≤ K ^ 6 at h51
      change |b ^ 4 * d ^ 2| ≤ K ^ 6 at h42
      change |b ^ 3 * d ^ 3| ≤ K ^ 6 at h33
      change |b ^ 2 * d ^ 4| ≤ K ^ 6 at h24
      change |b ^ 1 * d ^ 5| ≤ K ^ 6 at h15
      have hid : d * (b ^ 5 / 5 + b ^ 4 * d / 4 + b ^ 3 * d ^ 2 / 3 + b ^ 2 * d ^ 3 / 2 + b * d ^ 4) =
          (b ^ 5 * d ^ 1) / 5 + (b ^ 4 * d ^ 2) / 4 + (b ^ 3 * d ^ 3) / 3 +
            (b ^ 2 * d ^ 4) / 2 + (b ^ 1 * d ^ 5) := by ring
      rw [hid]
      obtain ⟨l1, u1⟩ := abs_le.mp h51
      obtain ⟨l2, u2⟩ := abs_le.mp h42
      obtain ⟨l3, u3⟩ := abs_le.mp h33
      obtain ⟨l4, u4⟩ := abs_le.mp h24
      obtain ⟨l5, u5⟩ := abs_le.mp h15
      rw [abs_le]; constructor <;> linarith
    let r_mid : ℝ → ℝ := fun t =>
      0 + b * (t - m) + (-(b ^ 2 / 2 + b * d)) * (t - m) ^ 2 +
        (b ^ 3 / 3 + b ^ 2 * d / 2 + b * d ^ 2) * (t - m) ^ 3 +
        (-(b ^ 4 / 4 + b ^ 3 * d / 3 + b ^ 2 * d ^ 2 / 2 + b * d ^ 3)) * (t - m) ^ 4 +
        (b ^ 5 / 5 + b ^ 4 * d / 4 + b ^ 3 * d ^ 2 / 3 + b ^ 2 * d ^ 3 / 2 + b * d ^ 4) * (t - m) ^ 5
    have hg2_pt : ∀ t ∈ Icc u v, |g2 t - r_mid t| ≤ 3 * K ^ 6 * (t - m) ^ 6 := by
      intro t ht
      obtain ⟨_, hbx, _, _, hd1⟩ := h_pt t ht
      have hd_pos : 0 < 1 + d * (t - m) := by linarith
      have hp5 := abs_log_one_add_sub_P5 (b * (t - m)) hbx
      have hbx6 : (b * (t - m)) ^ 6 ≤ K ^ 6 * (t - m) ^ 6 := by
        have hx6 : 0 ≤ (t - m) ^ 6 := by positivity
        have hb6 : b ^ 6 ≤ K ^ 6 := by
          have h1 : |b| ^ 6 ≤ K ^ 6 := by have := abs_nonneg b; gcongr
          have h2 : |b| ^ 6 = b ^ 6 := by
            rw [show (6 : ℕ) = 2 * 3 from rfl, pow_mul, pow_mul, sq_abs]
          linarith
        calc (b * (t - m)) ^ 6 = b ^ 6 * (t - m) ^ 6 := mul_pow b (t - m) 6
          _ ≤ K ^ 6 * (t - m) ^ 6 := mul_le_mul_of_nonneg_right hb6 hx6
      have htele : (1 + d * (t - m)) * r_mid t =
          ((b * (t - m)) - (b * (t - m)) ^ 2 / 2 + (b * (t - m)) ^ 3 / 3 -
            (b * (t - m)) ^ 4 / 4 + (b * (t - m)) ^ 5 / 5) +
          (d * (b ^ 5 / 5 + b ^ 4 * d / 4 + b ^ 3 * d ^ 2 / 3 + b ^ 2 * d ^ 3 / 2 + b * d ^ 4)) *
            (t - m) ^ 6 := by
        dsimp [r_mid]; ring
      have hnum : |Real.log (1 + b * (t - m)) - (1 + d * (t - m)) * r_mid t| ≤
          27 / 10 * K ^ 6 * (t - m) ^ 6 := by
        rw [htele]
        have hx6 : 0 ≤ (t - m) ^ 6 := by positivity
        obtain ⟨p1, p2⟩ := abs_le.mp hp5
        have hr_x : |(d * (b ^ 5 / 5 + b ^ 4 * d / 4 + b ^ 3 * d ^ 2 / 3 + b ^ 2 * d ^ 3 / 2 + b * d ^ 4)) *
            (t - m) ^ 6| ≤ 137 / 60 * K ^ 6 * (t - m) ^ 6 := by
          rw [abs_mul, abs_of_nonneg hx6]
          exact mul_le_mul_of_nonneg_right hrem hx6
        obtain ⟨rx1, rx2⟩ := abs_le.mp hr_x
        rw [abs_le]; constructor <;> linarith
      dsimp [g2]
      have hdiv_eq : Real.log (1 + b * (t - m)) / (1 + d * (t - m)) - r_mid t =
          (Real.log (1 + b * (t - m)) - (1 + d * (t - m)) * r_mid t) / (1 + d * (t - m)) := by
        exact div_sub' hd_pos.ne'
      rw [hdiv_eq, abs_div, abs_of_pos hd_pos, div_le_iff₀ hd_pos]
      have hx6 : 0 ≤ K ^ 6 * (t - m) ^ 6 := by positivity
      calc |Real.log (1 + b * (t - m)) - (1 + d * (t - m)) * r_mid t|
          ≤ 27 / 10 * (K ^ 6 * (t - m) ^ 6) := by linarith [hnum]
        _ = 3 * (K ^ 6 * (t - m) ^ 6) * (9 / 10) := by ring
        _ ≤ 3 * (K ^ 6 * (t - m) ^ 6) * (1 + d * (t - m)) :=
          mul_le_mul_of_nonneg_left hd1 (by positivity)
        _ = 3 * K ^ 6 * (t - m) ^ 6 * (1 + d * (t - m)) := by ring
    let r_lo_fn : ℝ → ℝ := fun t => r_mid t + (-3 * K ^ 6) * (t - m) ^ 6
    let r_hi_fn : ℝ → ℝ := fun t => r_mid t + (3 * K ^ 6) * (t - m) ^ 6
    have hm_lo : ∫ t in u..v, r_lo_fn t ≤ ∫ t in u..v, g2 t := by
      apply integral_mono_on huv (Continuous.intervalIntegrable (by fun_prop) _ _) hg2_int
      intro t ht
      have h1 := (abs_le.mp (hg2_pt t ht)).1
      dsimp [r_lo_fn]; linarith
    have hm_hi : ∫ t in u..v, g2 t ≤ ∫ t in u..v, r_hi_fn t := by
      apply integral_mono_on huv hg2_int (Continuous.intervalIntegrable (by fun_prop) _ _)
      intro t ht
      have h2 := (abs_le.mp (hg2_pt t ht)).2
      dsimp [r_hi_fn]; linarith
    have hev_lo := integral_centered_poly6 0 b (-(b ^ 2 / 2 + b * d))
      (b ^ 3 / 3 + b ^ 2 * d / 2 + b * d ^ 2)
      (-(b ^ 4 / 4 + b ^ 3 * d / 3 + b ^ 2 * d ^ 2 / 2 + b * d ^ 3))
      (b ^ 5 / 5 + b ^ 4 * d / 4 + b ^ 3 * d ^ 2 / 3 + b ^ 2 * d ^ 3 / 2 + b * d ^ 4)
      (-3 * K ^ 6) u v m h hm hh
    have hev_hi := integral_centered_poly6 0 b (-(b ^ 2 / 2 + b * d))
      (b ^ 3 / 3 + b ^ 2 * d / 2 + b * d ^ 2)
      (-(b ^ 4 / 4 + b ^ 3 * d / 3 + b ^ 2 * d ^ 2 / 2 + b * d ^ 3))
      (b ^ 5 / 5 + b ^ 4 * d / 4 + b ^ 3 * d ^ 2 / 3 + b ^ 2 * d ^ 3 / 2 + b * d ^ 4)
      (3 * K ^ 6) u v m h hm hh
    have h7 : 0 ≤ K ^ 6 * h ^ 7 := by positivity
    dsimp [r_lo_fn, r_mid] at hm_lo
    dsimp [r_hi_fn, r_mid] at hm_hi
    constructor <;> linarith
  refine ⟨hf_int, ?_, ?_⟩
  · rw [hsplit_eq]
    have hdiv := div_le_div_of_nonneg_right (add_le_add hLM_lo hg2_bounds.1) hN.le
    dsimp [quadLogLo] at hout_lo
    exact le_trans hout_lo hdiv
  · rw [hsplit_eq]
    have hdiv := div_le_div_of_nonneg_right (add_le_add hLM_hi hg2_bounds.2) hN.le
    dsimp [quadLogHi] at hout_hi
    exact le_trans hdiv hout_hi

def quadProdLo (m h b1 c0 c2 Alo Ahi Blo Bhi : ℝ) : ℝ :=
  (2 * h * c0 + 2 / 3 * h ^ 3 * c2 - 6 * h * ((Ahi - Alo) + (Bhi - Blo)) -
    28 / 5 * b1 ^ 4 * h ^ 5) / (m + 1)

private lemma continuous_centered_poly6 (a0 a1 a2 a3 a4 a5 a6 m : ℝ) :
    Continuous (fun t => a0 + a1 * (t - m) + a2 * (t - m) ^ 2 + a3 * (t - m) ^ 3 +
      a4 * (t - m) ^ 4 + a5 * (t - m) ^ 5 + a6 * (t - m) ^ 6) := by fun_prop

private lemma quad_prod_tele_err (x b1 b2 d c0 c1 c2 c3 Alo Blo : ℝ)
    (hb1_pos : 0 < b1) (hb2_pos : 0 < b2) (hd_pos0 : 0 < d)
    (hb2_le1 : b2 ≤ b1) (hd_le1 : d ≤ b1)
    (hx1 : |b1 * x| ≤ 1 / 10)
    (hc0 : c0 = Alo * Blo)
    (hc1 : c1 = Alo * b2 - Blo * b1 - d * c0)
    (hc2 : c2 = -Alo * b2 ^ 2 / 2 + Blo * b1 ^ 2 / 2 - b1 * b2 - d * c1)
    (hc3 : c3 = Alo * b2 ^ 3 / 3 - Blo * b1 ^ 3 / 3 + b1 * b2 ^ 2 / 2 + b1 ^ 2 * b2 / 2 - d * c2)
    (hAlo_abs : |Alo| ≤ 3 / 2) (hBlo_abs : |Blo| ≤ 1) :
    |(1 + d * x) * (c0 + c1 * x + c2 * x ^ 2 + c3 * x ^ 3) -
      (Alo - (b1 * x - (b1 * x) ^ 2 / 2 + (b1 * x) ^ 3 / 3)) *
        (Blo + (b2 * x - (b2 * x) ^ 2 / 2 + (b2 * x) ^ 3 / 3))| ≤
      11 * b1 ^ 4 * x ^ 4 := by
  have hc0_b : |c0| ≤ 3 / 2 := by
    rw [hc0, abs_mul]
    calc |Alo| * |Blo| ≤ (3 / 2) * 1 := mul_le_mul hAlo_abs hBlo_abs (abs_nonneg _) (by norm_num)
      _ = 3 / 2 := by norm_num
  have hc1_b : |c1| ≤ 4 * b1 := by
    rw [hc1]
    obtain ⟨l0, u0⟩ := abs_le.mp hc0_b
    obtain ⟨la, ua⟩ := abs_le.mp hAlo_abs
    obtain ⟨lb, ub⟩ := abs_le.mp hBlo_abs
    rw [abs_le]; constructor <;> nlinarith only [l0, u0, la, ua, lb, ub, hb1_pos, hb2_pos, hd_pos0, hb2_le1, hd_le1]
  have hc2_b : |c2| ≤ 7 * b1 ^ 2 := by
    rw [hc2]
    obtain ⟨la, ua⟩ := abs_le.mp hAlo_abs
    obtain ⟨lb, ub⟩ := abs_le.mp hBlo_abs
    have hb22 : b2 ^ 2 ≤ b1 ^ 2 := by gcongr
    have hb12 : b1 * b2 ≤ b1 ^ 2 := by nlinarith only [hb1_pos, hb2_le1]
    have hdc1 : |d * c1| ≤ 4 * b1 ^ 2 := by
      rw [abs_mul, abs_of_pos hd_pos0]
      calc d * |c1| ≤ b1 * (4 * b1) := mul_le_mul hd_le1 hc1_b (abs_nonneg _) hb1_pos.le
        _ = 4 * b1 ^ 2 := by ring
    obtain ⟨ld, ud⟩ := abs_le.mp hdc1
    have hb1sq : 0 ≤ b1 ^ 2 := sq_nonneg b1
    have hb2sq : 0 ≤ b2 ^ 2 := sq_nonneg b2
    have hb12_0 : 0 ≤ b1 * b2 := by positivity
    rw [abs_le]; constructor <;> nlinarith only [la, ua, lb, ub, hb22, hb12, ld, ud, hb1sq, hb2sq, hb12_0]
  have hc3_b : |c3| ≤ 9 * b1 ^ 3 := by
    rw [hc3]
    obtain ⟨la, ua⟩ := abs_le.mp hAlo_abs
    obtain ⟨lb, ub⟩ := abs_le.mp hBlo_abs
    have hb23 : b2 ^ 3 ≤ b1 ^ 3 := by gcongr
    have hb23_0 : 0 ≤ b2 ^ 3 := by positivity
    have hb13 : 0 ≤ b1 ^ 3 := by positivity
    have hm12 : b1 * b2 ^ 2 ≤ b1 ^ 3 := by
      have : b2 ^ 2 ≤ b1 ^ 2 := by gcongr
      nlinarith only [this, hb1_pos]
    have hm21 : b1 ^ 2 * b2 ≤ b1 ^ 3 := by have hsq := sq_nonneg b1; nlinarith only [hsq, hb2_le1]
    have hm12_0 : 0 ≤ b1 * b2 ^ 2 := by positivity
    have hm21_0 : 0 ≤ b1 ^ 2 * b2 := by positivity
    have hdc2 : |d * c2| ≤ 7 * b1 ^ 3 := by
      rw [abs_mul, abs_of_pos hd_pos0]
      calc d * |c2| ≤ b1 * (7 * b1 ^ 2) := mul_le_mul hd_le1 hc2_b (abs_nonneg _) hb1_pos.le
        _ = 7 * b1 ^ 3 := by ring
    obtain ⟨ld, ud⟩ := abs_le.mp hdc2
    rw [abs_le]; constructor <;> nlinarith only [la, ua, lb, ub, hb23, hb23_0, hb13, hm12, hm21, hm12_0, hm21_0, ld, ud]
  have htele : (1 + d * x) * (c0 + c1 * x + c2 * x ^ 2 + c3 * x ^ 3) -
      (Alo - (b1 * x - (b1 * x) ^ 2 / 2 + (b1 * x) ^ 3 / 3)) *
        (Blo + (b2 * x - (b2 * x) ^ 2 / 2 + (b2 * x) ^ 3 / 3)) =
      (d * c3 + b1 * b2 ^ 3 / 3 + b1 ^ 3 * b2 / 3 + b1 ^ 2 * b2 ^ 2 / 4) * x ^ 4 +
      (-b1 ^ 2 * b2 ^ 3 / 6 - b1 ^ 3 * b2 ^ 2 / 6) * x ^ 5 +
      (b1 ^ 3 * b2 ^ 3 / 9) * x ^ 6 := by
    rw [hc3, hc2, hc1, hc0]; ring
  rw [htele]
  have hdc3 : |d * c3| ≤ 9 * b1 ^ 4 := by
    rw [abs_mul, abs_of_pos hd_pos0]
    calc d * |c3| ≤ b1 * (9 * b1 ^ 3) := mul_le_mul hd_le1 hc3_b (abs_nonneg _) hb1_pos.le
      _ = 9 * b1 ^ 4 := by ring
  have hp13 : b1 * b2 ^ 3 ≤ b1 ^ 4 := by
    have : b2 ^ 3 ≤ b1 ^ 3 := by gcongr
    nlinarith only [this, hb1_pos]
  have hp31 : b1 ^ 3 * b2 ≤ b1 ^ 4 := by
    have : 0 ≤ b1 ^ 3 := by positivity
    nlinarith only [this, hb2_le1]
  have hp22 : b1 ^ 2 * b2 ^ 2 ≤ b1 ^ 4 := by
    have : b2 ^ 2 ≤ b1 ^ 2 := by gcongr
    have hsq := sq_nonneg b1
    nlinarith only [this, hsq]
  have hx4 : 0 ≤ x ^ 4 := by positivity
  have hc4_abs : |(d * c3 + b1 * b2 ^ 3 / 3 + b1 ^ 3 * b2 / 3 + b1 ^ 2 * b2 ^ 2 / 4) * x ^ 4| ≤
      10 * b1 ^ 4 * x ^ 4 := by
    rw [abs_mul, abs_of_nonneg hx4]
    apply mul_le_mul_of_nonneg_right _ hx4
    obtain ⟨l, u⟩ := abs_le.mp hdc3
    have z1 : 0 ≤ b1 ^ 4 := by positivity
    have z2 : 0 ≤ b1 ^ 2 * b2 ^ 2 := by positivity
    have z3 : 0 ≤ b1 * b2 ^ 3 := by positivity
    have z4 : 0 ≤ b1 ^ 3 * b2 := by positivity
    rw [abs_le]; constructor <;> linarith only [l, u, hp13, hp31, hp22, z1, z2, z3, z4]
  have hc5_abs : |(-b1 ^ 2 * b2 ^ 3 / 6 - b1 ^ 3 * b2 ^ 2 / 6) * x ^ 5| ≤
      1 / 2 * b1 ^ 4 * x ^ 4 := by
    have hx5_eq : |(-b1 ^ 2 * b2 ^ 3 / 6 - b1 ^ 3 * b2 ^ 2 / 6) * x ^ 5| =
        |-b1 ^ 2 * b2 ^ 3 / 6 - b1 ^ 3 * b2 ^ 2 / 6| * |x| * x ^ 4 := by
      have h5 : x ^ 5 = x * x ^ 4 := by ring
      rw [abs_mul, h5, abs_mul, abs_of_nonneg hx4, mul_assoc]
    rw [hx5_eq]
    apply mul_le_mul_of_nonneg_right _ hx4
    have hp23 : |-b1 ^ 2 * b2 ^ 3 / 6 - b1 ^ 3 * b2 ^ 2 / 6| ≤ b1 ^ 5 / 2 := by
      have t1 : b1 ^ 2 * b2 ^ 3 ≤ b1 ^ 5 := by
        have h3 : b2 ^ 3 ≤ b1 ^ 3 := by gcongr
        have hsq := sq_nonneg b1
        nlinarith only [h3, hsq]
      have t2 : b1 ^ 3 * b2 ^ 2 ≤ b1 ^ 5 := by
        have h2 : b2 ^ 2 ≤ b1 ^ 2 := by gcongr
        have h3 : 0 ≤ b1 ^ 3 := by positivity
        nlinarith only [h2, h3]
      have z1 : 0 ≤ b1 ^ 2 * b2 ^ 3 := by positivity
      have z2 : 0 ≤ b1 ^ 3 * b2 ^ 2 := by positivity
      have z3 : 0 ≤ b1 ^ 5 := by positivity
      rw [abs_le]; constructor <;> linarith only [t1, t2, z1, z2, z3]
    calc |-b1 ^ 2 * b2 ^ 3 / 6 - b1 ^ 3 * b2 ^ 2 / 6| * |x|
        ≤ (b1 ^ 5 / 2) * |x| := mul_le_mul_of_nonneg_right hp23 (abs_nonneg _)
      _ = b1 ^ 4 / 2 * (b1 * |x|) := by ring
      _ ≤ b1 ^ 4 / 2 * (1 / 10) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        rwa [← abs_of_pos hb1_pos, ← abs_mul]
      _ ≤ 1 / 2 * b1 ^ 4 := by
        have z4 : 0 ≤ b1 ^ 4 := by positivity
        linarith only [z4]
  have hc6_abs : |(b1 ^ 3 * b2 ^ 3 / 9) * x ^ 6| ≤ 1 / 2 * b1 ^ 4 * x ^ 4 := by
    rw [abs_mul, abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
    have hp33 : b1 ^ 3 * b2 ^ 3 ≤ b1 ^ 6 := by
      have h3 : b2 ^ 3 ≤ b1 ^ 3 := by gcongr
      have hb3 : 0 ≤ b1 ^ 3 := by positivity
      nlinarith only [h3, hb3]
    have hx2_le : b1 ^ 2 * x ^ 2 ≤ 1 / 100 := by
      obtain ⟨l1, u1⟩ := abs_le.mp hx1
      nlinarith only [l1, u1]
    have hb6_div : b1 ^ 3 * b2 ^ 3 / 9 ≤ b1 ^ 6 / 9 := by linarith only [hp33]
    have hx4b : 0 ≤ b1 ^ 4 * x ^ 4 := by positivity
    calc (b1 ^ 3 * b2 ^ 3 / 9) * x ^ 6
        ≤ (b1 ^ 6 / 9) * x ^ 6 := mul_le_mul_of_nonneg_right hb6_div (by positivity)
      _ = (b1 ^ 4 * x ^ 4 / 9) * (b1 ^ 2 * x ^ 2) := by ring
      _ ≤ (b1 ^ 4 * x ^ 4 / 9) * (1 / 100) :=
        mul_le_mul_of_nonneg_left hx2_le (by positivity)
      _ ≤ 1 / 2 * b1 ^ 4 * x ^ 4 := by linarith only [hx4b]
  have ht_tri : |(d * c3 + b1 * b2 ^ 3 / 3 + b1 ^ 3 * b2 / 3 + b1 ^ 2 * b2 ^ 2 / 4) * x ^ 4 +
      (-b1 ^ 2 * b2 ^ 3 / 6 - b1 ^ 3 * b2 ^ 2 / 6) * x ^ 5 +
      (b1 ^ 3 * b2 ^ 3 / 9) * x ^ 6| ≤
      |(d * c3 + b1 * b2 ^ 3 / 3 + b1 ^ 3 * b2 / 3 + b1 ^ 2 * b2 ^ 2 / 4) * x ^ 4| +
      |(-b1 ^ 2 * b2 ^ 3 / 6 - b1 ^ 3 * b2 ^ 2 / 6) * x ^ 5| +
      |(b1 ^ 3 * b2 ^ 3 / 9) * x ^ 6| :=
    le_trans (abs_add_le _ _) (add_le_add (abs_add_le _ _) le_rfl)
  linarith only [ht_tri, hc4_abs, hc5_abs, hc6_abs]

private lemma quad_prod_pt_lb (gb m t b1 b2 d c0 c1 c2 c3 Alo Ahi Blo Bhi : ℝ)
    (hm1 : 1 ≤ m) (hgb : 0 < gb)
    (hb1_pos : 0 < b1) (hb2_pos : 0 < b2) (hd_pos0 : 0 < d)
    (hb2_le1 : b2 ≤ b1) (hd_le1 : d ≤ b1)
    (ht_id : t = m * (1 + b1 * (t - m)))
    (ht2_id : (t + 2) / 3 = ((m + 2) / 3) * (1 + b2 * (t - m)))
    (ht1_id : t + 1 = (1 + d * (t - m)) * (m + 1))
    (hx1 : |b1 * (t - m)| ≤ 1 / 10) (hx2 : |b2 * (t - m)| ≤ 1 / 10)
    (hd1 : 9 / 10 ≤ 1 + d * (t - m)) (hb1_1 : 9 / 10 ≤ 1 + b1 * (t - m)) (hb2_1 : 9 / 10 ≤ 1 + b2 * (t - m))
    (hc0 : c0 = Alo * Blo)
    (hc1 : c1 = Alo * b2 - Blo * b1 - d * c0)
    (hc2 : c2 = -Alo * b2 ^ 2 / 2 + Blo * b1 ^ 2 / 2 - b1 * b2 - d * c1)
    (hc3 : c3 = Alo * b2 ^ 3 / 3 - Blo * b1 ^ 3 / 3 + b1 * b2 ^ 2 / 2 + b1 ^ 2 * b2 / 2 - d * c2)
    (hA_range : -1 / 10 ≤ Alo ∧ Alo ≤ 3 / 2 ∧ Ahi - Alo ≤ 1 / 100)
    (hB_range : 0 ≤ Blo ∧ Blo ≤ 1 ∧ Bhi - Blo ≤ 1 / 100)
    (hA : Alo ≤ Real.log (gb / m) ∧ Real.log (gb / m) ≤ Ahi)
    (hB : Blo ≤ Real.log ((m + 2) / 3) ∧ Real.log ((m + 2) / 3) ≤ Bhi) :
    ((c0 - 3 * ((Ahi - Alo) + (Bhi - Blo))) + c1 * (t - m) + c2 * (t - m) ^ 2 +
      c3 * (t - m) ^ 3 + (-14 * b1 ^ 4) * (t - m) ^ 4 + 0 * (t - m) ^ 5 + 0 * (t - m) ^ 6) / (m + 1) ≤
      Real.log (gb / t) * Real.log ((t + 2) / 3) / (t + 1) := by
  have hm_pos : 0 < m := by linarith only [hm1]
  have hm1_pos : 0 < m + 1 := by linarith only [hm1]
  have hd_pos : 0 < 1 + d * (t - m) := by linarith only [hd1]
  have hAlo_abs : |Alo| ≤ 3 / 2 := by
    rw [abs_le]; constructor <;> linarith only [hA_range.1, hA_range.2.1]
  have hBlo_abs : |Blo| ≤ 1 := by
    rw [abs_le]; constructor <;> linarith only [hB_range.1, hB_range.2.1]
  have hgbt_eq : gb / t = (gb / m) / (1 + b1 * (t - m)) := by
    conv_lhs => rw [ht_id]
    rw [div_mul_eq_div_div]
  have ha_val : Real.log (gb / t) = Real.log (gb / m) - Real.log (1 + b1 * (t - m)) := by
    rw [hgbt_eq, Real.log_div (div_pos hgb hm_pos).ne' (by linarith only [hb1_1])]
  have hb_val : Real.log ((t + 2) / 3) = Real.log ((m + 2) / 3) + Real.log (1 + b2 * (t - m)) := by
    rw [ht2_id, Real.log_mul (by positivity) (by linarith only [hb2_1])]
  have hp3_1 := abs_log_one_add_sub_P3 (b1 * (t - m)) hx1
  have hp3_2 := abs_log_one_add_sub_P3 (b2 * (t - m)) hx2
  have hb2x4 : (b2 * (t - m)) ^ 4 ≤ b1 ^ 4 * (t - m) ^ 4 := by
    have hx4 : 0 ≤ (t - m) ^ 4 := by positivity
    have hb24 : b2 ^ 4 ≤ b1 ^ 4 := by gcongr
    calc (b2 * (t - m)) ^ 4 = b2 ^ 4 * (t - m) ^ 4 := mul_pow b2 (t - m) 4
      _ ≤ b1 ^ 4 * (t - m) ^ 4 := mul_le_mul_of_nonneg_right hb24 hx4
  let pa := Alo - (b1 * (t - m) - (b1 * (t - m)) ^ 2 / 2 + (b1 * (t - m)) ^ 3 / 3)
  let pb := Blo + (b2 * (t - m) - (b2 * (t - m)) ^ 2 / 2 + (b2 * (t - m)) ^ 3 / 3)
  have ha_err : |Real.log (gb / t) - pa| ≤ (Ahi - Alo) + 5 / 18 * b1 ^ 4 * (t - m) ^ 4 := by
    rw [ha_val]
    obtain ⟨p1, p2⟩ := abs_le.mp hp3_1
    have hbx4 : (b1 * (t - m)) ^ 4 = b1 ^ 4 * (t - m) ^ 4 := mul_pow b1 (t - m) 4
    dsimp only [pa]
    rw [abs_le]; constructor <;> linarith only [p1, p2, hbx4, hA.1, hA.2]
  have hb_err : |Real.log ((t + 2) / 3) - pb| ≤ (Bhi - Blo) + 5 / 18 * b1 ^ 4 * (t - m) ^ 4 := by
    rw [hb_val]
    obtain ⟨p1, p2⟩ := abs_le.mp hp3_2
    dsimp only [pb]
    rw [abs_le]; constructor <;> linarith only [p1, p2, hb2x4, hB.1, hB.2]
  have hpa_abs : |pa| ≤ 2 := by
    obtain ⟨l1, u1⟩ := abs_le.mp hx1
    have h_p3 : |(b1 * (t - m)) - (b1 * (t - m)) ^ 2 / 2 + (b1 * (t - m)) ^ 3 / 3| ≤ 1 / 2 := by
      have hsq : (b1 * (t - m)) ^ 2 ≤ 1 / 100 := by nlinarith only [l1, u1]
      have hsq0 : 0 ≤ (b1 * (t - m)) ^ 2 := sq_nonneg _
      rw [abs_le]; constructor <;> nlinarith only [l1, u1, hsq, hsq0]
    obtain ⟨q1, q2⟩ := abs_le.mp h_p3
    dsimp only [pa]
    rw [abs_le]; constructor <;> linarith only [q1, q2, hA_range.1, hA_range.2.1]
  have hpb_abs : |pb| ≤ 6 / 5 := by
    obtain ⟨l2, u2⟩ := abs_le.mp hx2
    have h_p3 : |(b2 * (t - m)) - (b2 * (t - m)) ^ 2 / 2 + (b2 * (t - m)) ^ 3 / 3| ≤ 1 / 5 := by
      have hsq : (b2 * (t - m)) ^ 2 ≤ 1 / 100 := by nlinarith only [l2, u2]
      have hsq0 : 0 ≤ (b2 * (t - m)) ^ 2 := sq_nonneg _
      rw [abs_le]; constructor <;> nlinarith only [l2, u2, hsq, hsq0]
    obtain ⟨q1, q2⟩ := abs_le.mp h_p3
    dsimp only [pb]
    rw [abs_le]; constructor <;> linarith only [q1, q2, hB_range.1, hB_range.2.1]
  have hb_abs : |Real.log ((t + 2) / 3)| ≤ 5 / 4 := by
    have hx4_le : (b1 * (t - m)) ^ 4 ≤ 1 / 10000 := by
      obtain ⟨l1, u1⟩ := abs_le.mp hx1
      have hsq : (b1 * (t - m)) ^ 2 ≤ 1 / 100 := by nlinarith only [l1, u1]
      have hsq0 : 0 ≤ (b1 * (t - m)) ^ 2 := sq_nonneg _
      nlinarith only [hsq, hsq0]
    have heq4 := mul_pow b1 (t - m) 4
    have hbx4 : b1 ^ 4 * (t - m) ^ 4 ≤ 1 / 10000 := by linarith only [hx4_le, heq4]
    obtain ⟨e1, e2⟩ := abs_le.mp hb_err
    obtain ⟨p1, p2⟩ := abs_le.mp hpb_abs
    have hr2 := hB_range.2.2
    rw [abs_le]; constructor <;> linarith only [e1, e2, p1, p2, hbx4, hr2]
  have hepsA : 0 ≤ Ahi - Alo := by linarith only [hA.1, hA.2]
  have hepsB : 0 ≤ Bhi - Blo := by linarith only [hB.1, hB.2]
  have hx4_pos : 0 ≤ b1 ^ 4 * (t - m) ^ 4 := by positivity
  have hab_err : |Real.log (gb / t) * Real.log ((t + 2) / 3) - pa * pb| ≤
      2 * ((Ahi - Alo) + (Bhi - Blo)) + b1 ^ 4 * (t - m) ^ 4 := by
    have hid : Real.log (gb / t) * Real.log ((t + 2) / 3) - pa * pb =
        (Real.log (gb / t) - pa) * Real.log ((t + 2) / 3) + pa * (Real.log ((t + 2) / 3) - pb) := by ring
    rw [hid]
    have ht1 := abs_add_le ((Real.log (gb / t) - pa) * Real.log ((t + 2) / 3))
      (pa * (Real.log ((t + 2) / 3) - pb))
    rw [abs_mul, abs_mul] at ht1
    have hm1 : |Real.log (gb / t) - pa| * |Real.log ((t + 2) / 3)| ≤
        ((Ahi - Alo) + 5 / 18 * b1 ^ 4 * (t - m) ^ 4) * (5 / 4) :=
      mul_le_mul ha_err hb_abs (abs_nonneg _) (by positivity)
    have hm2 : |pa| * |Real.log ((t + 2) / 3) - pb| ≤ 2 * ((Bhi - Blo) + 5 / 18 * b1 ^ 4 * (t - m) ^ 4) :=
      mul_le_mul hpa_abs hb_err (abs_nonneg _) (by norm_num)
    linarith only [ht1, hm1, hm2, hepsA, hepsB, hx4_pos]
  have htele_err : |(1 + d * (t - m)) * (c0 + c1 * (t - m) + c2 * (t - m) ^ 2 + c3 * (t - m) ^ 3) - pa * pb| ≤
      11 * b1 ^ 4 * (t - m) ^ 4 :=
    quad_prod_tele_err (t - m) b1 b2 d c0 c1 c2 c3 Alo Blo hb1_pos hb2_pos hd_pos0 hb2_le1 hd_le1
      hx1 hc0 hc1 hc2 hc3 hAlo_abs hBlo_abs
  have h_inner : ((c0 - 3 * ((Ahi - Alo) + (Bhi - Blo))) + c1 * (t - m) + c2 * (t - m) ^ 2 +
      c3 * (t - m) ^ 3 + (-14 * b1 ^ 4) * (t - m) ^ 4 + 0 * (t - m) ^ 5 + 0 * (t - m) ^ 6) ≤
      Real.log (gb / t) * Real.log ((t + 2) / 3) / (1 + d * (t - m)) := by
    rw [le_div_iff₀ hd_pos]
    obtain ⟨a1, a2⟩ := abs_le.mp hab_err
    obtain ⟨t1, t2⟩ := abs_le.mp htele_err
    have hdiff : (1 + d * (t - m)) * (c0 + c1 * (t - m) + c2 * (t - m) ^ 2 + c3 * (t - m) ^ 3) -
        Real.log (gb / t) * Real.log ((t + 2) / 3) ≤
        2 * ((Ahi - Alo) + (Bhi - Blo)) + 12 * (b1 ^ 4 * (t - m) ^ 4) := by
      linarith only [a1, a2, t1, t2]
    have hscale : 2 * ((Ahi - Alo) + (Bhi - Blo)) + 12 * (b1 ^ 4 * (t - m) ^ 4) ≤
        (3 * ((Ahi - Alo) + (Bhi - Blo)) + 14 * b1 ^ 4 * (t - m) ^ 4) * (1 + d * (t - m)) := by
      have h_rhs0 : 0 ≤ 3 * ((Ahi - Alo) + (Bhi - Blo)) + 14 * b1 ^ 4 * (t - m) ^ 4 := by positivity
      have hm9 := mul_le_mul_of_nonneg_left hd1 h_rhs0
      linarith only [hm9, hepsA, hepsB, hx4_pos]
    have h_alg : ((c0 - 3 * ((Ahi - Alo) + (Bhi - Blo))) + c1 * (t - m) + c2 * (t - m) ^ 2 +
        c3 * (t - m) ^ 3 + (-14 * b1 ^ 4) * (t - m) ^ 4 + 0 * (t - m) ^ 5 + 0 * (t - m) ^ 6) * (1 + d * (t - m)) =
        (1 + d * (t - m)) * (c0 + c1 * (t - m) + c2 * (t - m) ^ 2 + c3 * (t - m) ^ 3) -
          (3 * ((Ahi - Alo) + (Bhi - Blo)) + 14 * b1 ^ 4 * (t - m) ^ 4) * (1 + d * (t - m)) := by ring
    linarith only [hdiff, hscale, h_alg]
  rw [ht1_id, ← div_div]
  exact div_le_div_of_nonneg_right h_inner hm1_pos.le

private lemma quad_prod_log_div_sub (gb M_gb M_m2 u v m h b1 b2 d c0 c1 c2 c3 Alo Ahi Blo Bhi out_lo : ℝ)
    (huv : u ≤ v)
    (hm : m = (u + v) / 2) (hh : h = (v - u) / 2)
    (hM_gb : M_gb = gb / m) (hM_m2 : M_m2 = (m + 2) / 3)
    (hm1 : 1 ≤ m) (hhm : b1 * h ≤ 1 / 10) (hgb : 0 < gb)
    (hb1_eq : m * b1 = 1) (hb2_eq : (m + 2) * b2 = 1) (hd_eq : (m + 1) * d = 1)
    (hc0 : c0 = Alo * Blo)
    (hc1 : c1 = Alo * b2 - Blo * b1 - d * c0)
    (hc2 : c2 = -Alo * b2 ^ 2 / 2 + Blo * b1 ^ 2 / 2 - b1 * b2 - d * c1)
    (hc3 : c3 = Alo * b2 ^ 3 / 3 - Blo * b1 ^ 3 / 3 + b1 * b2 ^ 2 / 2 + b1 ^ 2 * b2 / 2 - d * c2)
    (hA_range : -1 / 10 ≤ Alo ∧ Alo ≤ 3 / 2 ∧ Ahi - Alo ≤ 1 / 100)
    (hB_range : 0 ≤ Blo ∧ Blo ≤ 1 ∧ Bhi - Blo ≤ 1 / 100)
    (hA : Alo ≤ Real.log M_gb ∧ Real.log M_gb ≤ Ahi)
    (hB : Blo ≤ Real.log M_m2 ∧ Real.log M_m2 ≤ Bhi)
    (hout_lo : out_lo ≤ quadProdLo m h b1 c0 c2 Alo Ahi Blo Bhi) :
    IntervalIntegrable (fun t => Real.log (gb / t) * Real.log ((t + 2) / 3) / (t + 1)) volume u v ∧
      out_lo ≤ ∫ t in u..v, Real.log (gb / t) * Real.log ((t + 2) / 3) / (t + 1) := by
  rw [hM_gb] at hA
  rw [hM_m2] at hB
  have hm_pos : 0 < m := by linarith only [hm1]
  have hm1_pos : 0 < m + 1 := by linarith only [hm1]
  have hm2_pos : 0 < m + 2 := by linarith only [hm1]
  have hb1_pos : 0 < b1 := by nlinarith only [hm_pos, hb1_eq]
  have hb2_pos : 0 < b2 := by nlinarith only [hm2_pos, hb2_eq]
  have hd_pos0 : 0 < d := by nlinarith only [hm1_pos, hd_eq]
  have hb2_le1 : b2 ≤ b1 := by nlinarith only [hm_pos, hb1_pos, hb2_pos, hb1_eq, hb2_eq]
  have hd_le1 : d ≤ b1 := by nlinarith only [hm_pos, hb1_pos, hd_pos0, hb1_eq, hd_eq]
  have ht_id : ∀ t : ℝ, t = m * (1 + b1 * (t - m)) := fun t => by
    calc t = m + 1 * (t - m) := by ring
      _ = m + (m * b1) * (t - m) := by rw [hb1_eq]
      _ = m * (1 + b1 * (t - m)) := by ring
  have ht2_id : ∀ t : ℝ, (t + 2) / 3 = ((m + 2) / 3) * (1 + b2 * (t - m)) := fun t => by
    calc (t + 2) / 3 = ((m + 2) + 1 * (t - m)) / 3 := by ring
      _ = ((m + 2) + ((m + 2) * b2) * (t - m)) / 3 := by rw [hb2_eq]
      _ = ((m + 2) / 3) * (1 + b2 * (t - m)) := by ring
  have ht1_id : ∀ t : ℝ, t + 1 = (1 + d * (t - m)) * (m + 1) := fun t => by
    calc t + 1 = (m + 1) + 1 * (t - m) := by ring
      _ = (m + 1) + ((m + 1) * d) * (t - m) := by rw [hd_eq]
      _ = (1 + d * (t - m)) * (m + 1) := by ring
  have h_pt : ∀ t ∈ Icc u v, |t - m| ≤ h ∧ |b1 * (t - m)| ≤ 1 / 10 ∧
      |b2 * (t - m)| ≤ 1 / 10 ∧ |d * (t - m)| ≤ 1 / 10 ∧ 9 / 10 ≤ 1 + d * (t - m) ∧
      9 / 10 ≤ 1 + b1 * (t - m) ∧ 9 / 10 ≤ 1 + b2 * (t - m) := by
    intro t ht
    have htm : |t - m| ≤ h := by
      rw [abs_le]; constructor <;> linarith only [hm, hh, ht.1, ht.2]
    have hx1 : |b1 * (t - m)| ≤ 1 / 10 := by
      rw [abs_mul, abs_of_pos hb1_pos]
      exact le_trans (mul_le_mul_of_nonneg_left htm hb1_pos.le) hhm
    have hx2 : |b2 * (t - m)| ≤ 1 / 10 := by
      rw [abs_mul, abs_of_pos hb2_pos]
      calc b2 * |t - m| ≤ b1 * h := mul_le_mul hb2_le1 htm (abs_nonneg _) hb1_pos.le
        _ ≤ 1 / 10 := hhm
    have hxd : |d * (t - m)| ≤ 1 / 10 := by
      rw [abs_mul, abs_of_pos hd_pos0]
      calc d * |t - m| ≤ b1 * h := mul_le_mul hd_le1 htm (abs_nonneg _) hb1_pos.le
        _ ≤ 1 / 10 := hhm
    exact ⟨htm, hx1, hx2, hxd, by linarith only [(abs_le.mp hxd).1],
      by linarith only [(abs_le.mp hx1).1], by linarith only [(abs_le.mp hx2).1]⟩
  have hf_cont : ContinuousOn (fun t => Real.log (gb / t) * Real.log ((t + 2) / 3) / (t + 1)) (Icc u v) := by
    intro t ht
    obtain ⟨_, _, _, _, hd1, hb1_1, _⟩ := h_pt t ht
    have ht_pos : 0 < t := by rw [ht_id t]; positivity
    have ht_ne : t ≠ 0 := ht_pos.ne'
    have hgb_ne : gb / t ≠ 0 := (div_pos hgb ht_pos).ne'
    have ht2_ne : (t + 2) / 3 ≠ 0 := by positivity
    have ht1_ne : t + 1 ≠ 0 := by linarith only [ht_pos]
    exact ContinuousAt.continuousWithinAt (by fun_prop (disch := assumption))
  have hf_int : IntervalIntegrable (fun t => Real.log (gb / t) * Real.log ((t + 2) / 3) / (t + 1)) volume u v :=
    hf_cont.intervalIntegrable_of_Icc huv
  refine ⟨hf_int, ?_⟩
  have hpoly_int : IntervalIntegrable (fun t =>
      ((c0 - 3 * ((Ahi - Alo) + (Bhi - Blo))) + c1 * (t - m) + c2 * (t - m) ^ 2 +
        c3 * (t - m) ^ 3 + (-14 * b1 ^ 4) * (t - m) ^ 4 + 0 * (t - m) ^ 5 + 0 * (t - m) ^ 6) / (m + 1)) volume u v :=
    ((continuous_centered_poly6 (c0 - 3 * ((Ahi - Alo) + (Bhi - Blo))) c1 c2 c3 (-14 * b1 ^ 4) 0 0 m).div_const (m + 1)).intervalIntegrable u v
  have hmono : ∫ t in u..v, (((c0 - 3 * ((Ahi - Alo) + (Bhi - Blo))) + c1 * (t - m) + c2 * (t - m) ^ 2 +
      c3 * (t - m) ^ 3 + (-14 * b1 ^ 4) * (t - m) ^ 4 + 0 * (t - m) ^ 5 + 0 * (t - m) ^ 6) / (m + 1)) ≤
      ∫ t in u..v, Real.log (gb / t) * Real.log ((t + 2) / 3) / (t + 1) := by
    apply integral_mono_on huv hpoly_int hf_int
    intro t ht
    obtain ⟨_, hx1, hx2, _, hd1, hb1_1, hb2_1⟩ := h_pt t ht
    exact quad_prod_pt_lb gb m t b1 b2 d c0 c1 c2 c3 Alo Ahi Blo Bhi hm1 hgb hb1_pos hb2_pos hd_pos0
      hb2_le1 hd_le1 (ht_id t) (ht2_id t) (ht1_id t) hx1 hx2 hd1 hb1_1 hb2_1
      hc0 hc1 hc2 hc3 hA_range hB_range hA hB
  rw [intervalIntegral.integral_div] at hmono
  have hev := integral_centered_poly6 (c0 - 3 * ((Ahi - Alo) + (Bhi - Blo))) c1 c2 c3 (-14 * b1 ^ 4) 0 0 u v m h hm hh
  rw [hev] at hmono
  dsimp only [quadProdLo] at hout_lo
  refine le_trans hout_lo (le_trans ?_ hmono)
  apply div_le_div_of_nonneg_right _ hm1_pos.le
  linarith only []

private lemma chain_int_bounds {f : ℝ → ℝ} {u m v lo1 hi1 lo2 hi2 lo hi : ℝ}
    (h1 : IntervalIntegrable f volume u m ∧ lo1 ≤ ∫ t in u..m, f t ∧ ∫ t in u..m, f t ≤ hi1)
    (h2 : IntervalIntegrable f volume m v ∧ lo2 ≤ ∫ t in m..v, f t ∧ ∫ t in m..v, f t ≤ hi2)
    (hlo : lo ≤ lo1 + lo2) (hhi : hi1 + hi2 ≤ hi) :
    IntervalIntegrable f volume u v ∧ lo ≤ ∫ t in u..v, f t ∧ ∫ t in u..v, f t ≤ hi := by
  refine ⟨h1.1.trans h2.1, ?_, ?_⟩
  · rw [← integral_add_adjacent_intervals h1.1 h2.1]; linarith [h1.2.1, h2.2.1]
  · rw [← integral_add_adjacent_intervals h1.1 h2.1]; linarith [h1.2.2, h2.2.2]

private lemma chain_int_lb {f : ℝ → ℝ} {u m v lo1 lo2 lo : ℝ}
    (h1 : IntervalIntegrable f volume u m ∧ lo1 ≤ ∫ t in u..m, f t)
    (h2 : IntervalIntegrable f volume m v ∧ lo2 ≤ ∫ t in m..v, f t)
    (hlo : lo ≤ lo1 + lo2) :
    IntervalIntegrable f volume u v ∧ lo ≤ ∫ t in u..v, f t := by
  refine ⟨h1.1.trans h2.1, ?_⟩
  rw [← integral_add_adjacent_intervals h1.1 h2.1]; linarith [h1.2, h2.2]

private lemma int_inv_lin_pos (C D L R : ℝ) (hL : 0 < C + D * L) (hR : 0 < C + D * R)
    (hD : 0 < D) (hLR : L ≤ R) :
    IntervalIntegrable (fun t => 1 / (C + D * t)) volume L R ∧
      ∫ t in L..R, 1 / (C + D * t) = Real.log ((C + D * R) / (C + D * L)) / D := by
  have hpos : ∀ t ∈ uIcc L R, 0 < C + D * t := by
    rw [uIcc_of_le hLR]; intro t ht; nlinarith only [hL, hD, ht.1]
  have hint : IntervalIntegrable (fun t => 1 / (C + D * t)) volume L R := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    have hne : C + D * t ≠ 0 := (hpos t ht).ne'
    exact ContinuousAt.continuousWithinAt (by fun_prop (disch := exact hne))
  refine ⟨hint, ?_⟩
  let anti : ℝ → ℝ := fun t => Real.log (C + D * t) / D
  have hderiv : ∀ t ∈ uIcc L R, HasDerivAt anti (1 / (C + D * t)) t := by
    intro t ht
    have hp := hpos t ht
    have hd1 : HasDerivAt (fun t : ℝ => C + D * t) D t := by
      simpa using ((hasDerivAt_id t).const_mul D).const_add C
    refine ((hd1.log hp.ne').div_const D).congr_deriv ?_
    field_simp [hp.ne', hD.ne']
  rw [integral_eq_sub_of_hasDerivAt hderiv hint]
  dsimp [anti]
  rw [← sub_div, Real.log_div hR.ne' hL.ne']

private lemma int_inv_lin_neg (C D L R : ℝ) (hL : 0 < C + D * L) (hR : 0 < C + D * R)
    (hD : D < 0) (hLR : L ≤ R) :
    IntervalIntegrable (fun t => 1 / (C + D * t)) volume L R ∧
      ∫ t in L..R, 1 / (C + D * t) = Real.log ((C + D * L) / (C + D * R)) / (-D) := by
  have hpos : ∀ t ∈ uIcc L R, 0 < C + D * t := by
    rw [uIcc_of_le hLR]; intro t ht; nlinarith only [hR, hD, ht.2]
  have hint : IntervalIntegrable (fun t => 1 / (C + D * t)) volume L R := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    have hne : C + D * t ≠ 0 := (hpos t ht).ne'
    exact ContinuousAt.continuousWithinAt (by fun_prop (disch := exact hne))
  refine ⟨hint, ?_⟩
  let anti : ℝ → ℝ := fun t => Real.log (C + D * t) / D
  have hderiv : ∀ t ∈ uIcc L R, HasDerivAt anti (1 / (C + D * t)) t := by
    intro t ht
    have hp := hpos t ht
    have hd1 : HasDerivAt (fun t : ℝ => C + D * t) D t := by
      simpa using ((hasDerivAt_id t).const_mul D).const_add C
    refine ((hd1.log hp.ne').div_const D).congr_deriv ?_
    field_simp [hp.ne', hD.ne]
  rw [integral_eq_sub_of_hasDerivAt hderiv hint]
  dsimp [anti]
  have : Real.log (C + D * R) / D - Real.log (C + D * L) / D =
      (Real.log (C + D * L) - Real.log (C + D * R)) / (-D) := by
    have hnd : -D ≠ 0 := neg_ne_zero.mpr hD.ne
    field_simp [hD.ne, hnd]; ring
  rw [this, Real.log_div hL.ne' hR.ne']

private lemma sigma_eq_1d (t : ℝ) (ht : 1 ≤ t) :
    sigma 3 (t + 2) (t + 1) = ∫ s in (1 : ℝ)..t, Real.log ((s + 2) / 3) / (s + 1) := by
  unfold sigma
  have hshift := intervalIntegral.integral_comp_add_right
    (fun u => Real.log ((t + 1) / (u - 1)) / u) (2 : ℝ) (a := 1) (b := t)
  rw [(show (1 : ℝ) + 2 = 3 by norm_num)] at hshift
  rw [← hshift]
  let f1 : ℝ → ℝ := fun s => Real.log ((t + 1) / (s + 2 - 1)) / (s + 2)
  let f2 : ℝ → ℝ := fun s => Real.log ((s + 2) / 3) / (s + 1)
  have hf1_int : IntervalIntegrable f1 volume 1 t := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le ht]
    intro s hs
    have h0 : s + 2 - 1 ≠ 0 := by linarith [hs.1]
    have h1 : (t + 1) / (s + 2 - 1) ≠ 0 := by
      have : 0 < s + 2 - 1 := by linarith [hs.1]
      have : 0 < t + 1 := by linarith
      positivity
    have h2 : s + 2 ≠ 0 := by linarith [hs.1]
    exact ContinuousAt.continuousWithinAt (by dsimp [f1]; fun_prop (disch := assumption))
  have hf2_int : IntervalIntegrable f2 volume 1 t := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le ht]
    intro s hs
    have h1 : (s + 2) / 3 ≠ 0 := by linarith [hs.1]
    have h2 : s + 1 ≠ 0 := by linarith [hs.1]
    exact ContinuousAt.continuousWithinAt (by dsimp [f2]; fun_prop (disch := assumption))
  let D : ℝ → ℝ := fun s => (Real.log (t + 1) - Real.log (s + 1)) * (Real.log (s + 2) - Real.log 3)
  have hD_deriv : ∀ s ∈ uIcc 1 t, HasDerivAt D (f1 s - f2 s) s := by
    intro s hs
    rw [uIcc_of_le ht] at hs
    have hs1 : 0 < s + 1 := by linarith [hs.1]
    have hs2 : 0 < s + 2 := by linarith [hs.1]
    have ht1 : 0 < t + 1 := by linarith
    have dA : HasDerivAt (fun s => Real.log (t + 1) - Real.log (s + 1)) (-(1 / (s + 1))) s := by
      have dl : HasDerivAt (fun s => Real.log (s + 1)) (1 / (s + 1)) s := by
        simpa using ((hasDerivAt_id s).add_const 1).log hs1.ne'
      simpa using dl.const_sub (Real.log (t + 1))
    have dB : HasDerivAt (fun s => Real.log (s + 2) - Real.log 3) (1 / (s + 2)) s := by
      have dl : HasDerivAt (fun s => Real.log (s + 2)) (1 / (s + 2)) s := by
        simpa using ((hasDerivAt_id s).add_const 2).log hs2.ne'
      simpa using dl.sub_const (Real.log 3)
    refine (dA.mul dB).congr_deriv ?_
    dsimp [f1, f2]
    have hs21 : s + 2 - 1 = s + 1 := by ring
    rw [hs21, Real.log_div ht1.ne' hs1.ne', Real.log_div hs2.ne' (by norm_num)]
    ring
  have hftc := integral_eq_sub_of_hasDerivAt hD_deriv (hf1_int.sub hf2_int)
  rw [integral_sub hf1_int hf2_int] at hftc
  have hD1 : D 1 = 0 := by dsimp [D]; norm_num
  have hDt : D t = 0 := by dsimp [D]; ring
  rw [hD1, hDt] at hftc
  linarith

private lemma int_sigma_div_t (ga gb : ℝ) (h1 : 1 ≤ ga) (hab : ga ≤ gb) :
    IntervalIntegrable (fun t => sigma 3 (t + 2) (t + 1) / t) volume ga gb ∧
      ∫ t in ga..gb, sigma 3 (t + 2) (t + 1) / t =
        (∫ s in (1 : ℝ)..ga, Real.log ((s + 2) / 3) / (s + 1)) * Real.log (gb / ga) +
          ∫ t in ga..gb, Real.log (gb / t) * Real.log ((t + 2) / 3) / (t + 1) := by
  let f_F : ℝ → ℝ := fun s => Real.log (max 1 (s + 2) / 3) / max 1 (s + 1)
  have hfF_cont : Continuous f_F := by
    have hne1 : ∀ s : ℝ, max 1 (s + 2) / 3 ≠ 0 := fun s => by
      have : (0 : ℝ) < max 1 (s + 2) := lt_of_lt_of_le zero_lt_one (le_max_left 1 (s + 2))
      positivity
    have hne2 : ∀ s : ℝ, max 1 (s + 1) ≠ 0 := fun s =>
      (lt_of_lt_of_le zero_lt_one (le_max_left 1 (s + 1))).ne'
    dsimp [f_F]; fun_prop (disch := apply_assumption)
  let F : ℝ → ℝ := fun t => ∫ s in (1 : ℝ)..t, f_F s
  have hF_deriv : ∀ t : ℝ, HasDerivAt F (f_F t) t := fun t =>
    integral_hasDerivAt_right (hfF_cont.intervalIntegrable 1 t)
      hfF_cont.stronglyMeasurable.stronglyMeasurableAtFilter hfF_cont.continuousAt
  have hF_cont : Continuous F := Differentiable.continuous fun t => (hF_deriv t).differentiableAt
  have hF_eq : ∀ t, 1 ≤ t → F t = ∫ s in (1 : ℝ)..t, Real.log ((s + 2) / 3) / (s + 1) := by
    intro t ht
    apply integral_congr
    rw [uIcc_of_le ht]
    intro s hs
    dsimp [f_F]
    rw [max_eq_right (by linarith [hs.1]), max_eq_right (by linarith [hs.1])]
  let g1 : ℝ → ℝ := fun t => F t / t
  let g2 : ℝ → ℝ := fun t => Real.log (gb / t) * Real.log ((t + 2) / 3) / (t + 1)
  have hg1_int : IntervalIntegrable g1 volume ga gb := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hab]
    intro t ht
    have hne : t ≠ 0 := by linarith [h1, ht.1]
    exact ContinuousAt.continuousWithinAt (by dsimp [g1]; fun_prop (disch := exact hne))
  have hcongr_uIoc : EqOn g1 (fun t => sigma 3 (t + 2) (t + 1) / t) (uIoc ga gb) := by
    rw [uIoc_of_le hab]
    intro t ht
    dsimp [g1]
    have ht1 : 1 ≤ t := by linarith [h1, ht.1]
    rw [sigma_eq_1d t ht1, hF_eq t ht1]
  have hsig_int : IntervalIntegrable (fun t => sigma 3 (t + 2) (t + 1) / t) volume ga gb :=
    hg1_int.congr hcongr_uIoc
  refine ⟨hsig_int, ?_⟩
  have hcongr : EqOn (fun t => sigma 3 (t + 2) (t + 1) / t) g1 (uIcc ga gb) := by
    rw [uIcc_of_le hab]
    intro t ht
    dsimp [g1]
    have ht1 : 1 ≤ t := le_trans h1 ht.1
    rw [sigma_eq_1d t ht1, hF_eq t ht1]
  rw [integral_congr hcongr]
  have hg2_int : IntervalIntegrable g2 volume ga gb := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hab]
    intro t ht
    have ht_pos : 0 < t := by linarith [h1, ht.1]
    have ht_ne : t ≠ 0 := ht_pos.ne'
    have hgb_pos : 0 < gb := by linarith [h1, hab]
    have hne1 : gb / t ≠ 0 := (div_pos hgb_pos ht_pos).ne'
    have hne2 : (t + 2) / 3 ≠ 0 := by linarith [h1, ht.1]
    have hne3 : t + 1 ≠ 0 := by linarith [h1, ht.1]
    exact ContinuousAt.continuousWithinAt (by dsimp [g2]; fun_prop (disch := assumption))
  let W : ℝ → ℝ := fun t => F t * (Real.log t - Real.log gb)
  have hW_deriv : ∀ t ∈ uIcc ga gb, HasDerivAt W (g1 t - g2 t) t := by
    intro t ht
    rw [uIcc_of_le hab] at ht
    have ht_pos : 0 < t := by linarith [h1, ht.1]
    have hgb_pos : 0 < gb := by linarith [h1, hab]
    have dL : HasDerivAt (fun t => Real.log t - Real.log gb) (1 / t) t := by
      simpa using (Real.hasDerivAt_log ht_pos.ne').sub_const (Real.log gb)
    refine ((hF_deriv t).mul dL).congr_deriv ?_
    dsimp [g1, g2, f_F]
    rw [max_eq_right (by linarith [h1, ht.1]), max_eq_right (by linarith [h1, ht.1]),
      Real.log_div hgb_pos.ne' ht_pos.ne']
    ring
  have hftc := integral_eq_sub_of_hasDerivAt hW_deriv (hg1_int.sub hg2_int)
  rw [integral_sub hg1_int hg2_int] at hftc
  have hWgb : W gb = 0 := by dsimp [W]; ring
  have hWga : W ga = -(∫ s in (1 : ℝ)..ga, Real.log ((s + 2) / 3) / (s + 1)) * Real.log (gb / ga) := by
    dsimp [W]
    rw [hF_eq ga h1, Real.log_div (by linarith) (by linarith)]
    ring
  rw [hWgb, hWga] at hftc
  linarith

private lemma bound_sigma0_term (c Q ga gb GBA s354_lo s354_hi fga_lo gba_lo gba_hi j_lo q_lo q_hi out_lo : ℝ)
    (h1 : 1 ≤ ga) (hab : ga ≤ gb) (hc : 0 < c) (hGBA : GBA = gb / ga)
    (hs354 : IntervalIntegrable (fun s => Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * s) / (1 + 1 * s)) volume 1 3 ∧
      s354_lo ≤ ∫ s in (1 : ℝ)..3, Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * s) / (1 + 1 * s) ∧
      ∫ s in (1 : ℝ)..3, Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * s) / (1 + 1 * s) ≤ s354_hi)
    (hs354_lt1 : s354_hi < 1)
    (hfga : fga_lo ≤ ∫ s in (1 : ℝ)..ga, Real.log ((s + 2) / 3) / (s + 1))
    (hgba : gba_lo ≤ Real.log GBA ∧ Real.log GBA ≤ gba_hi)
    (hj : j_lo ≤ ∫ t in ga..gb, Real.log (gb / t) * Real.log ((t + 2) / 3) / (t + 1))
    (hq : q_lo ≤ Real.log Q ∧ Real.log Q ≤ q_hi)
    (hq_pos : 0 ≤ q_lo)
    (hnum_pos : 0 ≤ min (fga_lo * gba_lo) (fga_lo * gba_hi) + j_lo)
    (hout : out_lo ≤ ((min (fga_lo * gba_lo) (fga_lo * gba_hi) + j_lo) / (1 - s354_lo)) / c * q_lo) :
    IntervalIntegrable (fun t => sigma0 t / (c * t) * Real.log Q) volume ga gb ∧
      out_lo ≤ ∫ t in ga..gb, sigma0 t / (c * t) * Real.log Q := by
  rw [hGBA] at hgba
  obtain ⟨hsig_int, hsig_eq⟩ := int_sigma_div_t ga gb h1 hab
  have hs354_eq : sigma 3 5 4 = ∫ s in (1 : ℝ)..3, Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * s) / (1 + 1 * s) := by
    have h3 := sigma_eq_1d 3 (by norm_num)
    rw [(show (3 : ℝ) + 2 = 5 by norm_num), (show (3 : ℝ) + 1 = 4 by norm_num)] at h3
    rw [h3]
    apply integral_congr; intro s _; dsimp only; congr 1
    · congr 1; ring
    · ring
  have h1m_pos : 0 < 1 - sigma 3 5 4 := by rw [hs354_eq]; linarith [hs354.2.2]
  have h1m_lo : 0 < 1 - s354_lo := by rw [hs354_eq] at h1m_pos; linarith [hs354.2.1]
  have hcongr_fn : (fun t => sigma0 t / (c * t) * Real.log Q) =
      (fun t => (Real.log Q / (c * (1 - sigma 3 5 4))) * (sigma 3 (t + 2) (t + 1) / t)) := by
    ext t; unfold sigma0
    by_cases ht0 : t = 0
    · subst ht0; simp
    · field_simp [hc.ne', h1m_pos.ne', ht0]
  rw [hcongr_fn]
  refine ⟨hsig_int.const_mul _, ?_⟩
  rw [intervalIntegral.integral_const_mul, hsig_eq]
  have hgba_nn : 0 ≤ Real.log (gb / ga) := Real.log_nonneg ((one_le_div (by linarith)).mpr hab)
  have hp1 : min (fga_lo * gba_lo) (fga_lo * gba_hi) ≤
      (∫ s in (1 : ℝ)..ga, Real.log ((s + 2) / 3) / (s + 1)) * Real.log (gb / ga) := by
    have m1 := mul_le_mul_of_nonneg_right hfga hgba_nn
    have m2 := (mul_bounds_of_bounds (c := fga_lo) hgba.1 hgba.2).1
    linarith
  have hnum_le : min (fga_lo * gba_lo) (fga_lo * gba_hi) + j_lo ≤
      (∫ s in (1 : ℝ)..ga, Real.log ((s + 2) / 3) / (s + 1)) * Real.log (gb / ga) +
        ∫ t in ga..gb, Real.log (gb / t) * Real.log ((t + 2) / 3) / (t + 1) :=
    add_le_add hp1 hj
  have hden_le : 1 - sigma 3 5 4 ≤ 1 - s354_lo := by rw [hs354_eq]; linarith [hs354.2.1]
  have hdiv1 : (min (fga_lo * gba_lo) (fga_lo * gba_hi) + j_lo) / (1 - s354_lo) ≤
      ((∫ s in (1 : ℝ)..ga, Real.log ((s + 2) / 3) / (s + 1)) * Real.log (gb / ga) +
        ∫ t in ga..gb, Real.log (gb / t) * Real.log ((t + 2) / 3) / (t + 1)) / (1 - sigma 3 5 4) := by
    calc (min (fga_lo * gba_lo) (fga_lo * gba_hi) + j_lo) / (1 - s354_lo)
        ≤ (min (fga_lo * gba_lo) (fga_lo * gba_hi) + j_lo) / (1 - sigma 3 5 4) :=
          div_le_div_of_nonneg_left hnum_pos h1m_pos hden_le
      _ ≤ _ := div_le_div_of_nonneg_right hnum_le h1m_pos.le
  have hdiv2 : ((min (fga_lo * gba_lo) (fga_lo * gba_hi) + j_lo) / (1 - s354_lo)) / c * q_lo ≤
      (Real.log Q / (c * (1 - sigma 3 5 4))) *
        ((∫ s in (1 : ℝ)..ga, Real.log ((s + 2) / 3) / (s + 1)) * Real.log (gb / ga) +
          ∫ t in ga..gb, Real.log (gb / t) * Real.log ((t + 2) / 3) / (t + 1)) := by
    have hstep1 := mul_le_mul (div_le_div_of_nonneg_right hdiv1 hc.le) hq.1 hq_pos
      (div_nonneg (div_nonneg (le_trans hnum_pos hnum_le) h1m_pos.le) hc.le)
    have h_eq_rhs : (((∫ s in (1 : ℝ)..ga, Real.log ((s + 2) / 3) / (s + 1)) * Real.log (gb / ga) +
        ∫ t in ga..gb, Real.log (gb / t) * Real.log ((t + 2) / 3) / (t + 1)) / (1 - sigma 3 5 4)) / c * Real.log Q =
        (Real.log Q / (c * (1 - sigma 3 5 4))) *
        ((∫ s in (1 : ℝ)..ga, Real.log ((s + 2) / 3) / (s + 1)) * Real.log (gb / ga) +
          ∫ t in ga..gb, Real.log (gb / t) * Real.log ((t + 2) / 3) / (t + 1)) := by
      field_simp [hc.ne', h1m_pos.ne']
    rwa [← h_eq_rhs]
  exact le_trans hout hdiv2

private lemma integral_ind_zero (ga gb lo hi : ℝ) (f : ℝ → ℝ) (hab : ga ≤ gb)
    (hdisj : hi ≤ ga ∨ gb ≤ lo) :
    IntervalIntegrable (fun t => ind lo hi t * f t) volume ga gb ∧
      ∫ t in ga..gb, ind lo hi t * f t = 0 := by
  have hae_imp : ∀ᵐ t ∂volume, t ∈ uIoc ga gb → ind lo hi t * f t = 0 := by
    filter_upwards [compl_mem_ae_iff.mpr (measure_singleton gb)] with t htb ht
    rw [uIoc_of_le hab] at ht
    dsimp [ind]
    rw [if_neg]
    · ring
    · rcases hdisj with h1 | h2
      · intro h; linarith [ht.1, h.2]
      · intro h
        have hlt : t < gb := lt_of_le_of_ne ht.2 htb
        linarith [h.1]
  have hae_restr : (0 : ℝ → ℝ) =ᵐ[volume.restrict (uIoc ga gb)] (fun t => ind lo hi t * f t) := by
    rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_uIoc]
    filter_upwards [hae_imp] with t ht hmem using (ht hmem).symm
  have h0 : IntervalIntegrable (0 : ℝ → ℝ) volume ga gb := intervalIntegrable_const
  refine ⟨h0.congr_ae hae_restr, ?_⟩
  rw [intervalIntegral.integral_congr_ae hae_imp]
  simp

private lemma integral_ind_active (ga gb lo hi L R : ℝ) (f : ℝ → ℝ)
    (hgaL : ga ≤ L) (hLR : L ≤ R) (hRgb : R ≤ gb)
    (hloL : lo ≤ L) (hRhi : R ≤ hi)
    (hL_case : L = ga ∨ L = lo) (hR_case : R = gb ∨ R = hi)
    (hf : IntervalIntegrable f volume L R) :
    IntervalIntegrable (fun t => ind lo hi t * f t) volume ga gb ∧
      ∫ t in ga..gb, ind lo hi t * f t = ∫ t in L..R, f t := by
  have h1 : IntervalIntegrable (fun t => ind lo hi t * f t) volume ga L ∧
      ∫ t in ga..L, ind lo hi t * f t = 0 := by
    rcases hL_case with hL | hL
    · rw [hL]; exact ⟨IntervalIntegrable.refl, integral_same⟩
    · rw [hL] at hgaL ⊢; exact integral_ind_zero ga lo lo hi f hgaL (Or.inr le_rfl)
  have h2_eq : EqOn f (fun t => ind lo hi t * f t) (uIoc L R) := by
    rw [uIoc_of_le hLR]
    intro t ht
    dsimp [ind]
    rw [if_pos ⟨by linarith [ht.1], by linarith [ht.2]⟩, one_mul]
  have h2_int : IntervalIntegrable (fun t => ind lo hi t * f t) volume L R :=
    hf.congr h2_eq
  have h2_val : ∫ t in L..R, ind lo hi t * f t = ∫ t in L..R, f t := by
    apply integral_congr
    rw [uIcc_of_le hLR]
    intro t ht
    dsimp [ind]
    rw [if_pos ⟨by linarith [ht.1], by linarith [ht.2]⟩, one_mul]
  have h3 : IntervalIntegrable (fun t => ind lo hi t * f t) volume R gb ∧
      ∫ t in R..gb, ind lo hi t * f t = 0 := by
    rcases hR_case with hR | hR
    · rw [hR]; exact ⟨IntervalIntegrable.refl, integral_same⟩
    · rw [hR] at hRgb ⊢; exact integral_ind_zero hi gb lo hi f hRgb (Or.inl le_rfl)
  have h12_int := h1.1.trans h2_int
  refine ⟨h12_int.trans h3.1, ?_⟩
  rw [← integral_add_adjacent_intervals h12_int h3.1,
    ← integral_add_adjacent_intervals h1.1 h2_int, h1.2, h2_val, h3.2]
  ring

private lemma bound_ind_div_zero (ga gb lo hi : ℝ) (denom arg : ℝ → ℝ)
    (hab : ga ≤ gb) (hdisj : hi ≤ ga ∨ gb ≤ lo) :
    IntervalIntegrable (fun t => ind lo hi t / denom t * Real.log (arg t)) volume ga gb ∧
      (0 : ℝ) ≤ ∫ t in ga..gb, ind lo hi t / denom t * Real.log (arg t) := by
  have heq : (fun t => ind lo hi t / denom t * Real.log (arg t)) =
      (fun t => ind lo hi t * (Real.log (arg t) / denom t)) := by ext t; ring
  rw [heq]
  obtain ⟨h1, h2⟩ := integral_ind_zero ga gb lo hi (fun t => Real.log (arg t) / denom t) hab hdisj
  exact ⟨h1, by linarith⟩

private lemma bound_ind_div_active (ga gb lo hi L R out_lo : ℝ) (denom arg : ℝ → ℝ)
    (hgaL : ga ≤ L) (hLR : L ≤ R) (hRgb : R ≤ gb)
    (hloL : lo ≤ L) (hRhi : R ≤ hi)
    (hL_case : L = ga ∨ L = lo) (hR_case : R = gb ∨ R = hi)
    (hf : IntervalIntegrable (fun t => Real.log (arg t) / denom t) volume L R ∧
      out_lo ≤ ∫ t in L..R, Real.log (arg t) / denom t) :
    IntervalIntegrable (fun t => ind lo hi t / denom t * Real.log (arg t)) volume ga gb ∧
      out_lo ≤ ∫ t in ga..gb, ind lo hi t / denom t * Real.log (arg t) := by
  have heq : (fun t => ind lo hi t / denom t * Real.log (arg t)) =
      (fun t => ind lo hi t * (Real.log (arg t) / denom t)) := by ext t; ring
  rw [heq]
  obtain ⟨h1, h2⟩ := integral_ind_active ga gb lo hi L R (fun t => Real.log (arg t) / denom t)
    hgaL hLR hRgb hloL hRhi hL_case hR_case hf.1
  exact ⟨h1, by linarith [hf.2]⟩

private lemma active_t_pow (k : ℕ) (c Q L R RL q_lo q_hi r_lo r_hi i_lo i_hi out_lo : ℝ)
    (hL : 0 < L) (hLR : L ≤ R) (hc : 0 < c) (hQ : 0 < Q) (hRL_eq : RL = R / L)
    (hq : q_lo ≤ Real.log Q ∧ Real.log Q ≤ q_hi)
    (hr : r_lo ≤ Real.log RL ∧ Real.log RL ≤ r_hi)
    (hi1 : IntervalIntegrable (fun t => Real.log (1 + 1 * t) / (0 + 1 * t)) volume L R ∧
      i_lo ≤ ∫ t in L..R, Real.log (1 + 1 * t) / (0 + 1 * t) ∧
      ∫ t in L..R, Real.log (1 + 1 * t) / (0 + 1 * t) ≤ i_hi)
    (hout : out_lo ≤ min ((-q_hi / c) * r_lo) ((-q_hi / c) * r_hi) + ((k : ℝ) / c) * i_lo) :
    IntervalIntegrable (fun t => Real.log ((t + 1) ^ k / Q) / (c * t)) volume L R ∧
      out_lo ≤ ∫ t in L..R, Real.log ((t + 1) ^ k / Q) / (c * t) := by
  rw [hRL_eq] at hr
  obtain ⟨hinv_int, hinv_val⟩ := int_inv_lin_pos 0 1 L R (by linarith) (by linarith) zero_lt_one hLR
  have hcongr_uIoc : EqOn (fun t => (-Real.log Q / c) * (1 / (0 + 1 * t)) +
      ((k : ℝ) / c) * (Real.log (1 + 1 * t) / (0 + 1 * t)))
      (fun t => Real.log ((t + 1) ^ k / Q) / (c * t)) (uIoc L R) := by
    rw [uIoc_of_le hLR]; intro t ht; dsimp only
    have ht1 : 0 < t + 1 := by linarith [ht.1]
    have ht_ne : t ≠ 0 := by linarith [ht.1]
    rw [Real.log_div (pow_pos ht1 k).ne' hQ.ne', Real.log_pow]
    have h1t : 1 + 1 * t = t + 1 := by ring
    have h0t : 0 + 1 * t = t := by ring
    rw [h1t, h0t]
    field_simp [hc.ne', ht_ne]; ring
  have hsum_int := (hinv_int.const_mul (-Real.log Q / c)).add (hi1.1.const_mul ((k : ℝ) / c))
  refine ⟨hsum_int.congr hcongr_uIoc, ?_⟩
  have hcongr : EqOn (fun t => Real.log ((t + 1) ^ k / Q) / (c * t))
      (fun t => (-Real.log Q / c) * (1 / (0 + 1 * t)) +
        ((k : ℝ) / c) * (Real.log (1 + 1 * t) / (0 + 1 * t))) (uIcc L R) := by
    rw [uIcc_of_le hLR]; intro t ht; dsimp only
    have ht1 : 0 < t + 1 := by linarith [ht.1]
    have ht_ne : t ≠ 0 := by linarith [ht.1]
    rw [Real.log_div (pow_pos ht1 k).ne' hQ.ne', Real.log_pow]
    have h1t : 1 + 1 * t = t + 1 := by ring
    have h0t : 0 + 1 * t = t := by ring
    rw [h1t, h0t]
    field_simp [hc.ne', ht_ne]; ring
  rw [integral_congr hcongr, integral_add (hinv_int.const_mul _) (hi1.1.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, hinv_val]
  have hRL : (0 + 1 * R) / (0 + 1 * L) = R / L := by ring
  rw [hRL, div_one]
  have hr_nonneg : 0 ≤ Real.log (R / L) := Real.log_nonneg ((one_le_div hL).mpr hLR)
  have hq_div : -q_hi / c ≤ -Real.log Q / c := div_le_div_of_nonneg_right (by linarith [hq.2]) hc.le
  have h1 := mul_le_mul_of_nonneg_right hq_div hr_nonneg
  have h2 := (mul_bounds_of_bounds (c := -q_hi / c) hr.1 hr.2).1
  have h3 : ((k : ℝ) / c) * i_lo ≤ ((k : ℝ) / c) * ∫ t in L..R, Real.log (1 + 1 * t) / (0 + 1 * t) :=
    mul_le_mul_of_nonneg_left hi1.2.1 (by positivity)
  linarith

private lemma active_t_lin (c Q A2 L R RL q_lo q_hi r_lo r_hi i1_lo i1_hi i2_lo i2_hi out_lo : ℝ)
    (hL : 0 < L) (hLR : L ≤ R) (hA2 : R < A2) (hc : 0 < c) (hQ : 0 < Q) (hRL_eq : RL = R / L)
    (hq : q_lo ≤ Real.log Q ∧ Real.log Q ≤ q_hi)
    (hr : r_lo ≤ Real.log RL ∧ Real.log RL ≤ r_hi)
    (hi1 : IntervalIntegrable (fun t => Real.log (1 + 1 * t) / (0 + 1 * t)) volume L R ∧
      i1_lo ≤ ∫ t in L..R, Real.log (1 + 1 * t) / (0 + 1 * t) ∧
      ∫ t in L..R, Real.log (1 + 1 * t) / (0 + 1 * t) ≤ i1_hi)
    (hi2 : IntervalIntegrable (fun t => Real.log (A2 + (-1) * t) / (0 + 1 * t)) volume L R ∧
      i2_lo ≤ ∫ t in L..R, Real.log (A2 + (-1) * t) / (0 + 1 * t) ∧
      ∫ t in L..R, Real.log (A2 + (-1) * t) / (0 + 1 * t) ≤ i2_hi)
    (hout : out_lo ≤ min ((-q_hi / c) * r_lo) ((-q_hi / c) * r_hi) + (1 / c) * i1_lo - (1 / c) * i2_hi) :
    IntervalIntegrable (fun t => Real.log ((t + 1) / (Q * (A2 - t))) / (c * t)) volume L R ∧
      out_lo ≤ ∫ t in L..R, Real.log ((t + 1) / (Q * (A2 - t))) / (c * t) := by
  rw [hRL_eq] at hr
  obtain ⟨hinv_int, hinv_val⟩ := int_inv_lin_pos 0 1 L R (by linarith) (by linarith) zero_lt_one hLR
  let lin_comb : ℝ → ℝ := fun t =>
    (-Real.log Q / c) * (1 / (0 + 1 * t)) +
      (1 / c) * (Real.log (1 + 1 * t) / (0 + 1 * t)) -
      (1 / c) * (Real.log (A2 + (-1) * t) / (0 + 1 * t))
  have hsum_int : IntervalIntegrable lin_comb volume L R :=
    ((hinv_int.const_mul _).add (hi1.1.const_mul _)).sub (hi2.1.const_mul _)
  have hcongr_Icc : EqOn lin_comb (fun t => Real.log ((t + 1) / (Q * (A2 - t))) / (c * t)) (Icc L R) := by
    intro t ht
    dsimp [lin_comb]
    have ht1 : 0 < t + 1 := by linarith [ht.1]
    have hAt : 0 < A2 - t := by linarith [ht.2]
    have ht_ne : t ≠ 0 := by linarith [ht.1]
    rw [Real.log_div ht1.ne' (mul_pos hQ hAt).ne', Real.log_mul hQ.ne' hAt.ne']
    have h1t : 1 + 1 * t = t + 1 := by ring
    have h2t : A2 + (-1) * t = A2 - t := by ring
    have h0t : 0 + 1 * t = t := by ring
    rw [h1t, h2t, h0t]
    field_simp [hc.ne', ht_ne]; ring
  have hcongr_uIoc : EqOn lin_comb (fun t => Real.log ((t + 1) / (Q * (A2 - t))) / (c * t)) (uIoc L R) := by
    rw [uIoc_of_le hLR]; exact hcongr_Icc.mono Ioc_subset_Icc_self
  refine ⟨hsum_int.congr hcongr_uIoc, ?_⟩
  have hcongr_uIcc : EqOn (fun t => Real.log ((t + 1) / (Q * (A2 - t))) / (c * t)) lin_comb (uIcc L R) := by
    rw [uIcc_of_le hLR]; exact hcongr_Icc.symm
  rw [integral_congr hcongr_uIcc]
  dsimp [lin_comb]
  rw [integral_sub ((hinv_int.const_mul _).add (hi1.1.const_mul _)) (hi2.1.const_mul _),
    integral_add (hinv_int.const_mul _) (hi1.1.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, hinv_val]
  have hRL : (0 + 1 * R) / (0 + 1 * L) = R / L := by ring
  rw [hRL, div_one]
  have hr_nonneg : 0 ≤ Real.log (R / L) := Real.log_nonneg ((one_le_div hL).mpr hLR)
  have hq_div : -q_hi / c ≤ -Real.log Q / c := div_le_div_of_nonneg_right (by linarith [hq.2]) hc.le
  have h1 := mul_le_mul_of_nonneg_right hq_div hr_nonneg
  have h2 := (mul_bounds_of_bounds (c := -q_hi / c) hr.1 hr.2).1
  have h3 : (1 / c) * i1_lo ≤ (1 / c) * ∫ t in L..R, Real.log (1 + 1 * t) / (0 + 1 * t) :=
    mul_le_mul_of_nonneg_left hi1.2.1 (by positivity)
  have h4 : (1 / c) * ∫ t in L..R, Real.log (A2 + (-1) * t) / (0 + 1 * t) ≤ (1 / c) * i2_hi :=
    mul_le_mul_of_nonneg_left hi2.2.2 (by positivity)
  linarith

private lemma int_q_const (sp L R rt_lo rt_hi rs_lo rs_hi : ℝ)
    (hL : 0 < L) (hLR : L ≤ R) (hRsp : R < sp)
    (hrt : rt_lo ≤ Real.log (R / L) ∧ Real.log (R / L) ≤ rt_hi)
    (hrs : rs_lo ≤ Real.log ((sp - L) / (sp - R)) ∧ Real.log ((sp - L) / (sp - R)) ≤ rs_hi) :
    IntervalIntegrable (fun t => 1 / (5 * t * (1 - t / sp))) volume L R ∧
      0 ≤ ∫ t in L..R, 1 / (5 * t * (1 - t / sp)) ∧
      (rt_lo + rs_lo) / 5 ≤ ∫ t in L..R, 1 / (5 * t * (1 - t / sp)) := by
  obtain ⟨h1_int, h1_val⟩ := int_inv_lin_pos 0 1 L R (by linarith) (by linarith) zero_lt_one hLR
  obtain ⟨h2_int, h2_val⟩ := int_inv_lin_neg sp (-1) L R (by linarith) (by linarith) (by norm_num) hLR
  let comb : ℝ → ℝ := fun t => (1 / 5) * (1 / (0 + 1 * t)) + (1 / 5) * (1 / (sp + (-1) * t))
  have hcomb_int : IntervalIntegrable comb volume L R :=
    (h1_int.const_mul _).add (h2_int.const_mul _)
  have h_eq : EqOn comb (fun t => 1 / (5 * t * (1 - t / sp))) (Icc L R) := by
    intro t ht
    dsimp [comb]
    have ht_ne : t ≠ 0 := by linarith [ht.1]
    have hsp_ne : sp ≠ 0 := by linarith
    have hspt_ne : sp - t ≠ 0 := by linarith [ht.2]
    have h1mts : 1 - t / sp ≠ 0 := by
      intro h; apply hspt_ne; have := sub_eq_zero.mp h; field_simp [hsp_ne] at this; linarith
    have h0t : 0 + 1 * t = t := by ring
    have hspt : sp + (-1) * t = sp - t := by ring
    rw [h0t, hspt]
    field_simp [ht_ne, hsp_ne, hspt_ne, h1mts]; ring
  have h_int := hcomb_int.congr (by rw [uIoc_of_le hLR]; exact h_eq.mono Ioc_subset_Icc_self)
  have h_val : ∫ t in L..R, 1 / (5 * t * (1 - t / sp)) =
      (Real.log (R / L) + Real.log ((sp - L) / (sp - R))) / 5 := by
    rw [integral_congr (by rw [uIcc_of_le hLR]; exact h_eq.symm)]
    dsimp [comb]
    rw [integral_add (h1_int.const_mul _) (h2_int.const_mul _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, h1_val, h2_val]
    have e1 : (0 + 1 * R) / (0 + 1 * L) = R / L := by ring
    have e2 : (sp + (-1) * L) / (sp + (-1) * R) = (sp - L) / (sp - R) := by ring
    rw [e1, e2]
    ring
  have hnn1 : 0 ≤ Real.log (R / L) := Real.log_nonneg ((one_le_div hL).mpr hLR)
  have hnn2 : 0 ≤ Real.log ((sp - L) / (sp - R)) :=
    Real.log_nonneg ((one_le_div (by linarith)).mpr (by linarith))
  refine ⟨h_int, by rw [h_val]; positivity, by rw [h_val]; linarith [hrt.1, hrs.1]⟩

private lemma int_q_log (sp A B L R i1_lo i1_hi i2_lo i2_hi : ℝ)
    (hL : 0 < L) (hLR : L ≤ R) (hRsp : R < sp)
    (hi1 : IntervalIntegrable (fun t => Real.log (A + B * t) / (0 + 1 * t)) volume L R ∧
      i1_lo ≤ ∫ t in L..R, Real.log (A + B * t) / (0 + 1 * t) ∧
      ∫ t in L..R, Real.log (A + B * t) / (0 + 1 * t) ≤ i1_hi)
    (hi2 : IntervalIntegrable (fun t => Real.log (A + B * t) / (sp + (-1) * t)) volume L R ∧
      i2_lo ≤ ∫ t in L..R, Real.log (A + B * t) / (sp + (-1) * t) ∧
      ∫ t in L..R, Real.log (A + B * t) / (sp + (-1) * t) ≤ i2_hi) :
    IntervalIntegrable (fun t => Real.log (A + B * t) / (5 * t * (1 - t / sp))) volume L R ∧
      (i1_lo + i2_lo) / 5 ≤ ∫ t in L..R, Real.log (A + B * t) / (5 * t * (1 - t / sp)) ∧
      ∫ t in L..R, Real.log (A + B * t) / (5 * t * (1 - t / sp)) ≤ (i1_hi + i2_hi) / 5 := by
  let comb : ℝ → ℝ := fun t =>
    (1 / 5) * (Real.log (A + B * t) / (0 + 1 * t)) +
      (1 / 5) * (Real.log (A + B * t) / (sp + (-1) * t))
  have hcomb_int : IntervalIntegrable comb volume L R :=
    (hi1.1.const_mul _).add (hi2.1.const_mul _)
  have h_eq : EqOn comb (fun t => Real.log (A + B * t) / (5 * t * (1 - t / sp))) (Icc L R) := by
    intro t ht
    dsimp [comb]
    have ht_ne : t ≠ 0 := by linarith [ht.1]
    have hsp_ne : sp ≠ 0 := by linarith
    have hspt_ne : sp - t ≠ 0 := by linarith [ht.2]
    have h1mts : 1 - t / sp ≠ 0 := by
      intro h; apply hspt_ne; have := sub_eq_zero.mp h; field_simp [hsp_ne] at this; linarith
    have h0t : 0 + 1 * t = t := by ring
    have hspt : sp + (-1) * t = sp - t := by ring
    rw [h0t, hspt]
    field_simp [ht_ne, hsp_ne, hspt_ne, h1mts]; ring
  have h_int := hcomb_int.congr (by rw [uIoc_of_le hLR]; exact h_eq.mono Ioc_subset_Icc_self)
  have h_val : ∫ t in L..R, Real.log (A + B * t) / (5 * t * (1 - t / sp)) =
      ((∫ t in L..R, Real.log (A + B * t) / (0 + 1 * t)) +
        ∫ t in L..R, Real.log (A + B * t) / (sp + (-1) * t)) / 5 := by
    calc ∫ t in L..R, Real.log (A + B * t) / (5 * t * (1 - t / sp))
        = ∫ t in L..R, comb t := integral_congr (by rw [uIcc_of_le hLR]; exact h_eq.symm)
      _ = (∫ t in L..R, (1 / 5) * (Real.log (A + B * t) / (0 + 1 * t))) +
            ∫ t in L..R, (1 / 5) * (Real.log (A + B * t) / (sp + (-1) * t)) :=
          integral_add (hi1.1.const_mul _) (hi2.1.const_mul _)
      _ = (1 / 5) * (∫ t in L..R, Real.log (A + B * t) / (0 + 1 * t)) +
            (1 / 5) * (∫ t in L..R, Real.log (A + B * t) / (sp + (-1) * t)) := by
          rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
      _ = _ := by ring
  refine ⟨h_int, by rw [h_val]; linarith [hi1.2.1, hi2.2.1], by rw [h_val]; linarith [hi1.2.2, hi2.2.2]⟩

private lemma active_q_6 (sp k1 k3 A1 B1 A2 B2 L R RL SLR sp_lo sp_hi rt_lo rt_hi rs_lo rs_hi
    a1_lo a1_hi a2_lo a2_hi b1_lo b1_hi b2_lo b2_hi out_lo : ℝ)
    (hL : 0 < L) (hLR : L ≤ R) (hRsp : R < sp) (hsp_lo : 0 ≤ sp_lo)
    (hA1 : A1 = k1 * sp - sp) (hB1 : B1 = -k1)
    (hA2 : A2 = k3 * sp - sp) (hB2 : B2 = -k3)
    (hk1R : 0 < k1 * sp - sp - k1 * R) (hk1_pos : 0 < k1)
    (hk3R : 0 < k3 * sp - sp - k3 * R) (hk3_pos : 0 < k3)
    (hRL_eq : RL = R / L) (hSLR_eq : SLR = (sp - L) / (sp - R))
    (hsp : sp_lo ≤ Real.log sp ∧ Real.log sp ≤ sp_hi)
    (hrt : rt_lo ≤ Real.log RL ∧ Real.log RL ≤ rt_hi)
    (hrs : rs_lo ≤ Real.log SLR ∧ Real.log SLR ≤ rs_hi)
    (ha1 : IntervalIntegrable (fun t => Real.log (A1 + B1 * t) / (0 + 1 * t)) volume L R ∧
      a1_lo ≤ ∫ t in L..R, Real.log (A1 + B1 * t) / (0 + 1 * t) ∧
      ∫ t in L..R, Real.log (A1 + B1 * t) / (0 + 1 * t) ≤ a1_hi)
    (ha2 : IntervalIntegrable (fun t => Real.log (A1 + B1 * t) / (sp + (-1) * t)) volume L R ∧
      a2_lo ≤ ∫ t in L..R, Real.log (A1 + B1 * t) / (sp + (-1) * t) ∧
      ∫ t in L..R, Real.log (A1 + B1 * t) / (sp + (-1) * t) ≤ a2_hi)
    (hb1 : IntervalIntegrable (fun t => Real.log (A2 + B2 * t) / (0 + 1 * t)) volume L R ∧
      b1_lo ≤ ∫ t in L..R, Real.log (A2 + B2 * t) / (0 + 1 * t) ∧
      ∫ t in L..R, Real.log (A2 + B2 * t) / (0 + 1 * t) ≤ b1_hi)
    (hb2 : IntervalIntegrable (fun t => Real.log (A2 + B2 * t) / (sp + (-1) * t)) volume L R ∧
      b2_lo ≤ ∫ t in L..R, Real.log (A2 + B2 * t) / (sp + (-1) * t) ∧
      ∫ t in L..R, Real.log (A2 + B2 * t) / (sp + (-1) * t) ≤ b2_hi)
    (hout : out_lo ≤ 2 * sp_lo * ((rt_lo + rs_lo) / 5) - (a1_hi + a2_hi) / 5 - (b1_hi + b2_hi) / 5) :
    IntervalIntegrable (fun t => Real.log (sp ^ 2 / ((k1 * sp - sp - k1 * t) * (k3 * sp - sp - k3 * t))) /
      (5 * t * (1 - t / sp))) volume L R ∧
      out_lo ≤ ∫ t in L..R, Real.log (sp ^ 2 / ((k1 * sp - sp - k1 * t) * (k3 * sp - sp - k3 * t))) /
        (5 * t * (1 - t / sp)) := by
  rw [hRL_eq] at hrt; rw [hSLR_eq] at hrs
  obtain ⟨hc_int, hc_nn, hc_lo⟩ := int_q_const sp L R rt_lo rt_hi rs_lo rs_hi hL hLR hRsp hrt hrs
  obtain ⟨ha_int, _, ha_hi⟩ := int_q_log sp A1 B1 L R a1_lo a1_hi a2_lo a2_hi hL hLR hRsp ha1 ha2
  obtain ⟨hb_int, _, hb_hi⟩ := int_q_log sp A2 B2 L R b1_lo b1_hi b2_lo b2_hi hL hLR hRsp hb1 hb2
  let comb : ℝ → ℝ := fun t =>
    (2 * Real.log sp) * (1 / (5 * t * (1 - t / sp))) -
      Real.log (A1 + B1 * t) / (5 * t * (1 - t / sp)) -
      Real.log (A2 + B2 * t) / (5 * t * (1 - t / sp))
  have hcomb_int : IntervalIntegrable comb volume L R :=
    ((hc_int.const_mul _).sub ha_int).sub hb_int
  have h_eq : EqOn comb (fun t => Real.log (sp ^ 2 / ((k1 * sp - sp - k1 * t) * (k3 * sp - sp - k3 * t))) /
      (5 * t * (1 - t / sp))) (Icc L R) := by
    intro t ht
    dsimp [comb]
    have hsp_pos : 0 < sp := by linarith
    have hd1 : 0 < k1 * sp - sp - k1 * t := by nlinarith only [hk1R, hk1_pos, ht.2]
    have hd2 : 0 < k3 * sp - sp - k3 * t := by nlinarith only [hk3R, hk3_pos, ht.2]
    rw [Real.log_div (pow_pos hsp_pos 2).ne' (mul_pos hd1 hd2).ne',
      Real.log_pow, Real.log_mul hd1.ne' hd2.ne']
    have e1 : A1 + B1 * t = k1 * sp - sp - k1 * t := by rw [hA1, hB1]; ring
    have e2 : A2 + B2 * t = k3 * sp - sp - k3 * t := by rw [hA2, hB2]; ring
    rw [e1, e2]; ring
  refine ⟨hcomb_int.congr (by rw [uIoc_of_le hLR]; exact h_eq.mono Ioc_subset_Icc_self), ?_⟩
  have hval : ∫ t in L..R, Real.log (sp ^ 2 / ((k1 * sp - sp - k1 * t) * (k3 * sp - sp - k3 * t))) /
      (5 * t * (1 - t / sp)) =
      (2 * Real.log sp) * (∫ t in L..R, 1 / (5 * t * (1 - t / sp))) -
      (∫ t in L..R, Real.log (A1 + B1 * t) / (5 * t * (1 - t / sp))) -
      (∫ t in L..R, Real.log (A2 + B2 * t) / (5 * t * (1 - t / sp))) := by
    calc _ = ∫ t in L..R, comb t := integral_congr (by rw [uIcc_of_le hLR]; exact h_eq.symm)
      _ = (∫ t in L..R, ((2 * Real.log sp) * (1 / (5 * t * (1 - t / sp))) -
            Real.log (A1 + B1 * t) / (5 * t * (1 - t / sp)))) -
            ∫ t in L..R, Real.log (A2 + B2 * t) / (5 * t * (1 - t / sp)) :=
          integral_sub ((hc_int.const_mul _).sub ha_int) hb_int
      _ = (∫ t in L..R, (2 * Real.log sp) * (1 / (5 * t * (1 - t / sp)))) -
            (∫ t in L..R, Real.log (A1 + B1 * t) / (5 * t * (1 - t / sp))) -
            ∫ t in L..R, Real.log (A2 + B2 * t) / (5 * t * (1 - t / sp)) := by
          rw [integral_sub (hc_int.const_mul _) ha_int]
      _ = _ := by rw [intervalIntegral.integral_const_mul]
  rw [hval]
  have hm1 : 2 * sp_lo * ((rt_lo + rs_lo) / 5) ≤ (2 * Real.log sp) * ∫ t in L..R, 1 / (5 * t * (1 - t / sp)) := by
    calc 2 * sp_lo * ((rt_lo + rs_lo) / 5)
        ≤ (2 * sp_lo) * ∫ t in L..R, 1 / (5 * t * (1 - t / sp)) :=
          mul_le_mul_of_nonneg_left hc_lo (by linarith)
      _ ≤ (2 * Real.log sp) * ∫ t in L..R, 1 / (5 * t * (1 - t / sp)) :=
          mul_le_mul_of_nonneg_right (by linarith [hsp.1]) hc_nn
  linarith

private lemma active_q_7 (sp k1 A1 A2 B2 L R RL SLR sp_lo sp_hi rt_lo rt_hi rs_lo rs_hi
    a1_lo a1_hi a2_lo a2_hi b1_lo b1_hi b2_lo b2_hi out_lo : ℝ)
    (hL : 0 < L) (hLR : L ≤ R) (hRsp1 : R < sp - 1) (hsp_lo : 0 ≤ sp_lo)
    (hA1 : A1 = sp - 1) (hA2 : A2 = k1 * sp - sp) (hB2 : B2 = -k1)
    (hk1R : 0 < k1 * sp - sp - k1 * R) (hk1_pos : 0 < k1)
    (hRL_eq : RL = R / L) (hSLR_eq : SLR = (sp - L) / (sp - R))
    (hsp : sp_lo ≤ Real.log sp ∧ Real.log sp ≤ sp_hi)
    (hrt : rt_lo ≤ Real.log RL ∧ Real.log RL ≤ rt_hi)
    (hrs : rs_lo ≤ Real.log SLR ∧ Real.log SLR ≤ rs_hi)
    (ha1 : IntervalIntegrable (fun t => Real.log (A1 + (-1) * t) / (0 + 1 * t)) volume L R ∧
      a1_lo ≤ ∫ t in L..R, Real.log (A1 + (-1) * t) / (0 + 1 * t) ∧
      ∫ t in L..R, Real.log (A1 + (-1) * t) / (0 + 1 * t) ≤ a1_hi)
    (ha2 : IntervalIntegrable (fun t => Real.log (A1 + (-1) * t) / (sp + (-1) * t)) volume L R ∧
      a2_lo ≤ ∫ t in L..R, Real.log (A1 + (-1) * t) / (sp + (-1) * t) ∧
      ∫ t in L..R, Real.log (A1 + (-1) * t) / (sp + (-1) * t) ≤ a2_hi)
    (hb1 : IntervalIntegrable (fun t => Real.log (A2 + B2 * t) / (0 + 1 * t)) volume L R ∧
      b1_lo ≤ ∫ t in L..R, Real.log (A2 + B2 * t) / (0 + 1 * t) ∧
      ∫ t in L..R, Real.log (A2 + B2 * t) / (0 + 1 * t) ≤ b1_hi)
    (hb2 : IntervalIntegrable (fun t => Real.log (A2 + B2 * t) / (sp + (-1) * t)) volume L R ∧
      b2_lo ≤ ∫ t in L..R, Real.log (A2 + B2 * t) / (sp + (-1) * t) ∧
      ∫ t in L..R, Real.log (A2 + B2 * t) / (sp + (-1) * t) ≤ b2_hi)
    (hout : out_lo ≤ sp_lo * ((rt_lo + rs_lo) / 5) + (a1_lo + a2_lo) / 5 - (b1_hi + b2_hi) / 5) :
    IntervalIntegrable (fun t => Real.log (sp * (sp - 1 - t) / (k1 * sp - sp - k1 * t)) /
      (5 * t * (1 - t / sp))) volume L R ∧
      out_lo ≤ ∫ t in L..R, Real.log (sp * (sp - 1 - t) / (k1 * sp - sp - k1 * t)) /
        (5 * t * (1 - t / sp)) := by
  rw [hRL_eq] at hrt; rw [hSLR_eq] at hrs
  have hRsp : R < sp := by linarith
  obtain ⟨hc_int, hc_nn, hc_lo⟩ := int_q_const sp L R rt_lo rt_hi rs_lo rs_hi hL hLR hRsp hrt hrs
  obtain ⟨ha_int, ha_lo, _⟩ := int_q_log sp A1 (-1) L R a1_lo a1_hi a2_lo a2_hi hL hLR hRsp ha1 ha2
  obtain ⟨hb_int, _, hb_hi⟩ := int_q_log sp A2 B2 L R b1_lo b1_hi b2_lo b2_hi hL hLR hRsp hb1 hb2
  let comb : ℝ → ℝ := fun t =>
    Real.log sp * (1 / (5 * t * (1 - t / sp))) +
      Real.log (A1 + (-1) * t) / (5 * t * (1 - t / sp)) -
      Real.log (A2 + B2 * t) / (5 * t * (1 - t / sp))
  have hcomb_int : IntervalIntegrable comb volume L R :=
    ((hc_int.const_mul _).add ha_int).sub hb_int
  have h_eq : EqOn comb (fun t => Real.log (sp * (sp - 1 - t) / (k1 * sp - sp - k1 * t)) /
      (5 * t * (1 - t / sp))) (Icc L R) := by
    intro t ht
    dsimp [comb]
    have hsp_pos : 0 < sp := by linarith
    have hd1 : 0 < sp - 1 - t := by linarith [ht.2]
    have hd2 : 0 < k1 * sp - sp - k1 * t := by nlinarith only [hk1R, hk1_pos, ht.2]
    rw [Real.log_div (mul_pos hsp_pos hd1).ne' hd2.ne', Real.log_mul hsp_pos.ne' hd1.ne']
    have e1 : A1 + (-1) * t = sp - 1 - t := by rw [hA1]; ring
    have e2 : A2 + B2 * t = k1 * sp - sp - k1 * t := by rw [hA2, hB2]; ring
    rw [e1, e2]; ring
  refine ⟨hcomb_int.congr (by rw [uIoc_of_le hLR]; exact h_eq.mono Ioc_subset_Icc_self), ?_⟩
  have hval : ∫ t in L..R, Real.log (sp * (sp - 1 - t) / (k1 * sp - sp - k1 * t)) /
      (5 * t * (1 - t / sp)) =
      Real.log sp * (∫ t in L..R, 1 / (5 * t * (1 - t / sp))) +
      (∫ t in L..R, Real.log (A1 + (-1) * t) / (5 * t * (1 - t / sp))) -
      (∫ t in L..R, Real.log (A2 + B2 * t) / (5 * t * (1 - t / sp))) := by
    calc _ = ∫ t in L..R, comb t := integral_congr (by rw [uIcc_of_le hLR]; exact h_eq.symm)
      _ = (∫ t in L..R, (Real.log sp * (1 / (5 * t * (1 - t / sp))) +
            Real.log (A1 + (-1) * t) / (5 * t * (1 - t / sp)))) -
            ∫ t in L..R, Real.log (A2 + B2 * t) / (5 * t * (1 - t / sp)) :=
          integral_sub ((hc_int.const_mul _).add ha_int) hb_int
      _ = (∫ t in L..R, Real.log sp * (1 / (5 * t * (1 - t / sp)))) +
            (∫ t in L..R, Real.log (A1 + (-1) * t) / (5 * t * (1 - t / sp))) -
            ∫ t in L..R, Real.log (A2 + B2 * t) / (5 * t * (1 - t / sp)) := by
          rw [integral_add (hc_int.const_mul _) ha_int]
      _ = _ := by rw [intervalIntegral.integral_const_mul]
  rw [hval]
  have hm1 : sp_lo * ((rt_lo + rs_lo) / 5) ≤ Real.log sp * ∫ t in L..R, 1 / (5 * t * (1 - t / sp)) := by
    calc sp_lo * ((rt_lo + rs_lo) / 5)
        ≤ sp_lo * ∫ t in L..R, 1 / (5 * t * (1 - t / sp)) := mul_le_mul_of_nonneg_left hc_lo hsp_lo
      _ ≤ Real.log sp * ∫ t in L..R, 1 / (5 * t * (1 - t / sp)) :=
          mul_le_mul_of_nonneg_right hsp.1 hc_nn
  linarith

private lemma active_q_8 (sp k2 A1 B1 L R RL SLR sp_lo sp_hi rt_lo rt_hi rs_lo rs_hi
    a1_lo a1_hi a2_lo a2_hi out_lo : ℝ)
    (hL : 0 < L) (hLR : L ≤ R) (hRsp : R < sp) (hsp_lo : 0 ≤ sp_lo)
    (hA1 : A1 = k2 * sp - sp) (hB1 : B1 = -k2)
    (hk2R : 0 < k2 * sp - sp - k2 * R) (hk2_pos : 0 < k2)
    (hRL_eq : RL = R / L) (hSLR_eq : SLR = (sp - L) / (sp - R))
    (hsp : sp_lo ≤ Real.log sp ∧ Real.log sp ≤ sp_hi)
    (hrt : rt_lo ≤ Real.log RL ∧ Real.log RL ≤ rt_hi)
    (hrs : rs_lo ≤ Real.log SLR ∧ Real.log SLR ≤ rs_hi)
    (ha1 : IntervalIntegrable (fun t => Real.log (A1 + B1 * t) / (0 + 1 * t)) volume L R ∧
      a1_lo ≤ ∫ t in L..R, Real.log (A1 + B1 * t) / (0 + 1 * t) ∧
      ∫ t in L..R, Real.log (A1 + B1 * t) / (0 + 1 * t) ≤ a1_hi)
    (ha2 : IntervalIntegrable (fun t => Real.log (A1 + B1 * t) / (sp + (-1) * t)) volume L R ∧
      a2_lo ≤ ∫ t in L..R, Real.log (A1 + B1 * t) / (sp + (-1) * t) ∧
      ∫ t in L..R, Real.log (A1 + B1 * t) / (sp + (-1) * t) ≤ a2_hi)
    (hout : out_lo ≤ sp_lo * ((rt_lo + rs_lo) / 5) - (a1_hi + a2_hi) / 5) :
    IntervalIntegrable (fun t => Real.log (sp / (k2 * sp - sp - k2 * t)) /
      (5 * t * (1 - t / sp))) volume L R ∧
      out_lo ≤ ∫ t in L..R, Real.log (sp / (k2 * sp - sp - k2 * t)) /
        (5 * t * (1 - t / sp)) := by
  rw [hRL_eq] at hrt; rw [hSLR_eq] at hrs
  obtain ⟨hc_int, hc_nn, hc_lo⟩ := int_q_const sp L R rt_lo rt_hi rs_lo rs_hi hL hLR hRsp hrt hrs
  obtain ⟨ha_int, _, ha_hi⟩ := int_q_log sp A1 B1 L R a1_lo a1_hi a2_lo a2_hi hL hLR hRsp ha1 ha2
  let comb : ℝ → ℝ := fun t =>
    Real.log sp * (1 / (5 * t * (1 - t / sp))) -
      Real.log (A1 + B1 * t) / (5 * t * (1 - t / sp))
  have hcomb_int : IntervalIntegrable comb volume L R :=
    (hc_int.const_mul _).sub ha_int
  have h_eq : EqOn comb (fun t => Real.log (sp / (k2 * sp - sp - k2 * t)) /
      (5 * t * (1 - t / sp))) (Icc L R) := by
    intro t ht
    dsimp [comb]
    have hsp_pos : 0 < sp := by linarith
    have hd1 : 0 < k2 * sp - sp - k2 * t := by nlinarith only [hk2R, hk2_pos, ht.2]
    rw [Real.log_div hsp_pos.ne' hd1.ne']
    have e1 : A1 + B1 * t = k2 * sp - sp - k2 * t := by rw [hA1, hB1]; ring
    rw [e1]; ring
  refine ⟨hcomb_int.congr (by rw [uIoc_of_le hLR]; exact h_eq.mono Ioc_subset_Icc_self), ?_⟩
  have hval : ∫ t in L..R, Real.log (sp / (k2 * sp - sp - k2 * t)) / (5 * t * (1 - t / sp)) =
      Real.log sp * (∫ t in L..R, 1 / (5 * t * (1 - t / sp))) -
      (∫ t in L..R, Real.log (A1 + B1 * t) / (5 * t * (1 - t / sp))) := by
    calc _ = ∫ t in L..R, comb t := integral_congr (by rw [uIcc_of_le hLR]; exact h_eq.symm)
      _ = (∫ t in L..R, Real.log sp * (1 / (5 * t * (1 - t / sp)))) -
            ∫ t in L..R, Real.log (A1 + B1 * t) / (5 * t * (1 - t / sp)) :=
          integral_sub (hc_int.const_mul _) ha_int
      _ = _ := by rw [intervalIntegral.integral_const_mul]
  rw [hval]
  have hm1 : sp_lo * ((rt_lo + rs_lo) / 5) ≤ Real.log sp * ∫ t in L..R, 1 / (5 * t * (1 - t / sp)) := by
    calc sp_lo * ((rt_lo + rs_lo) / 5)
        ≤ sp_lo * ∫ t in L..R, 1 / (5 * t * (1 - t / sp)) := mul_le_mul_of_nonneg_left hc_lo hsp_lo
      _ ≤ Real.log sp * ∫ t in L..R, 1 / (5 * t * (1 - t / sp)) :=
          mul_le_mul_of_nonneg_right hsp.1 hc_nn
  linarith

private lemma active_q_9 (sp A1 L R a1_lo a1_hi a2_lo a2_hi out_lo : ℝ)
    (hL : 0 < L) (hLR : L ≤ R) (hRsp : R < sp) (hA1 : A1 = sp - 1)
    (ha1 : IntervalIntegrable (fun t => Real.log (A1 + (-1) * t) / (0 + 1 * t)) volume L R ∧
      a1_lo ≤ ∫ t in L..R, Real.log (A1 + (-1) * t) / (0 + 1 * t) ∧
      ∫ t in L..R, Real.log (A1 + (-1) * t) / (0 + 1 * t) ≤ a1_hi)
    (ha2 : IntervalIntegrable (fun t => Real.log (A1 + (-1) * t) / (sp + (-1) * t)) volume L R ∧
      a2_lo ≤ ∫ t in L..R, Real.log (A1 + (-1) * t) / (sp + (-1) * t) ∧
      ∫ t in L..R, Real.log (A1 + (-1) * t) / (sp + (-1) * t) ≤ a2_hi)
    (hout : out_lo ≤ (a1_lo + a2_lo) / 5) :
    IntervalIntegrable (fun t => Real.log (sp - 1 - t) / (5 * t * (1 - t / sp))) volume L R ∧
      out_lo ≤ ∫ t in L..R, Real.log (sp - 1 - t) / (5 * t * (1 - t / sp)) := by
  obtain ⟨ha_int, ha_lo, _⟩ := int_q_log sp A1 (-1) L R a1_lo a1_hi a2_lo a2_hi hL hLR hRsp ha1 ha2
  have heq : (fun t => Real.log (sp - 1 - t) / (5 * t * (1 - t / sp))) =
      (fun t => Real.log (A1 + (-1) * t) / (5 * t * (1 - t / sp))) := by
    ext t; congr 2; rw [hA1]; ring
  rw [heq]
  exact ⟨ha_int, le_trans hout ha_lo⟩


private lemma add_int_lb {f g : ℝ → ℝ} {a b l1 l2 l : ℝ}
    (hf : IntervalIntegrable f volume a b ∧ l1 ≤ ∫ t in a..b, f t)
    (hg : IntervalIntegrable g volume a b ∧ l2 ≤ ∫ t in a..b, g t)
    (hl : l ≤ l1 + l2) :
    IntervalIntegrable (fun t => f t + g t) volume a b ∧ l ≤ ∫ t in a..b, (f t + g t) :=
  ⟨hf.1.add hg.1, by rw [integral_add hf.1 hg.1]; linarith [hf.2, hg.2]⟩

private lemma hlog_1 : (206192872023 / 10000000000000 : ℝ) ≤ Real.log (49 / 48 : ℝ) ∧ Real.log (49 / 48 : ℝ) ≤ (6443527251 / 312500000000 : ℝ) :=
  log_rat_bounds (49 / 48 : ℝ) (1 / 244 : ℝ) (-4) (4) (-1) (206192872023 / 10000000000000 : ℝ) (6443527251 / 312500000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hqsub_2 :
    IntervalIntegrable (fun t => Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t)) volume (1 : ℝ) (9 / 8 : ℝ) ∧
      (12333251771 / 10000000000000 : ℝ) ≤ ∫ t in (1 : ℝ)..(9 / 8 : ℝ), Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (1 : ℝ)..(9 / 8 : ℝ), Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t) ≤ (12333252243 / 10000000000000 : ℝ) :=
  quad_log_div_sub (2 / 3 : ℝ) (1 / 3 : ℝ) (1 : ℝ) (1 : ℝ) (1 : ℝ) (9 / 8 : ℝ) (17 / 16 : ℝ) (1 / 16 : ℝ)
    (49 / 48 : ℝ) (33 / 16 : ℝ) (16 / 49 : ℝ) (16 / 33 : ℝ) (16 / 33 : ℝ) (206192872023 / 10000000000000 : ℝ) (6443527251 / 312500000000 : ℝ) (12333251771 / 10000000000000 : ℝ) (12333252243 / 10000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog_1 (by norm_num [quadLogLo]) (by norm_num [quadLogHi])

private lemma hlog_3 : (7578077727 / 125000000000 : ℝ) ≤ Real.log (17 / 16 : ℝ) ∧ Real.log (17 / 16 : ℝ) ≤ (606246218169 / 10000000000000 : ℝ) :=
  log_rat_bounds (17 / 16 : ℝ) (1 / 271 : ℝ) (-7) (3) (1) (7578077727 / 125000000000 : ℝ) (606246218169 / 10000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hqsub_4 :
    IntervalIntegrable (fun t => Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t)) volume (9 / 8 : ℝ) (5 / 4 : ℝ) ∧
      (6901732827 / 2000000000000 : ℝ) ≤ ∫ t in (9 / 8 : ℝ)..(5 / 4 : ℝ), Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (9 / 8 : ℝ)..(5 / 4 : ℝ), Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t) ≤ (34508664451 / 10000000000000 : ℝ) :=
  quad_log_div_sub (2 / 3 : ℝ) (1 / 3 : ℝ) (1 : ℝ) (1 : ℝ) (9 / 8 : ℝ) (5 / 4 : ℝ) (19 / 16 : ℝ) (1 / 16 : ℝ)
    (17 / 16 : ℝ) (35 / 16 : ℝ) (16 / 51 : ℝ) (16 / 35 : ℝ) (16 / 35 : ℝ) (7578077727 / 125000000000 : ℝ) (606246218169 / 10000000000000 : ℝ) (6901732827 / 2000000000000 : ℝ) (34508664451 / 10000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog_3 (by norm_num [quadLogLo]) (by norm_num [quadLogHi])

private lemma hlog_5 : (990909026439 / 10000000000000 : ℝ) ≤ Real.log (53 / 48 : ℝ) ∧ Real.log (53 / 48 : ℝ) ≤ (495454513223 / 5000000000000 : ℝ) :=
  log_rat_bounds (53 / 48 : ℝ) (29 / 2621 : ℝ) (0) (3) (-2) (990909026439 / 10000000000000 : ℝ) (495454513223 / 5000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hqsub_6 :
    IntervalIntegrable (fun t => Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t)) volume (5 / 4 : ℝ) (11 / 8 : ℝ) ∧
      (53451679461 / 10000000000000 : ℝ) ≤ ∫ t in (5 / 4 : ℝ)..(11 / 8 : ℝ), Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (5 / 4 : ℝ)..(11 / 8 : ℝ), Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t) ≤ (13362919919 / 2500000000000 : ℝ) :=
  quad_log_div_sub (2 / 3 : ℝ) (1 / 3 : ℝ) (1 : ℝ) (1 : ℝ) (5 / 4 : ℝ) (11 / 8 : ℝ) (21 / 16 : ℝ) (1 / 16 : ℝ)
    (53 / 48 : ℝ) (37 / 16 : ℝ) (16 / 53 : ℝ) (16 / 37 : ℝ) (16 / 37 : ℝ) (990909026439 / 10000000000000 : ℝ) (495454513223 / 5000000000000 : ℝ) (53451679461 / 10000000000000 : ℝ) (13362919919 / 2500000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog_5 (by norm_num [quadLogLo]) (by norm_num [quadLogHi])

private lemma hlog_7 : (1361321743243 / 10000000000000 : ℝ) ≤ Real.log (55 / 48 : ℝ) ∧ Real.log (55 / 48 : ℝ) ≤ (85082608953 / 625000000000 : ℝ) :=
  log_rat_bounds (55 / 48 : ℝ) (1 / 109 : ℝ) (-3) (2) (0) (1361321743243 / 10000000000000 : ℝ) (85082608953 / 625000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hqsub_8 :
    IntervalIntegrable (fun t => Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t)) volume (11 / 8 : ℝ) (3 / 2 : ℝ) ∧
      (69718679241 / 10000000000000 : ℝ) ≤ ∫ t in (11 / 8 : ℝ)..(3 / 2 : ℝ), Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (11 / 8 : ℝ)..(3 / 2 : ℝ), Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t) ≤ (2178708731 / 312500000000 : ℝ) :=
  quad_log_div_sub (2 / 3 : ℝ) (1 / 3 : ℝ) (1 : ℝ) (1 : ℝ) (11 / 8 : ℝ) (3 / 2 : ℝ) (23 / 16 : ℝ) (1 / 16 : ℝ)
    (55 / 48 : ℝ) (39 / 16 : ℝ) (16 / 55 : ℝ) (16 / 39 : ℝ) (16 / 39 : ℝ) (1361321743243 / 10000000000000 : ℝ) (85082608953 / 625000000000 : ℝ) (69718679241 / 10000000000000 : ℝ) (2178708731 / 312500000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog_7 (by norm_num [quadLogLo]) (by norm_num [quadLogHi])

private lemma hlog_9 : (1718502569263 / 10000000000000 : ℝ) ≤ Real.log (19 / 16 : ℝ) ∧ Real.log (19 / 16 : ℝ) ≤ (171850256927 / 1000000000000 : ℝ) :=
  log_rat_bounds (19 / 16 : ℝ) (1 / 1025 : ℝ) (5) (-3) (0) (1718502569263 / 10000000000000 : ℝ) (171850256927 / 1000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hqsub_10 :
    IntervalIntegrable (fun t => Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t)) volume (3 / 2 : ℝ) (13 / 8 : ℝ) ∧
      (10468922707 / 1250000000000 : ℝ) ≤ ∫ t in (3 / 2 : ℝ)..(13 / 8 : ℝ), Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (3 / 2 : ℝ)..(13 / 8 : ℝ), Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t) ≤ (83751381763 / 10000000000000 : ℝ) :=
  quad_log_div_sub (2 / 3 : ℝ) (1 / 3 : ℝ) (1 : ℝ) (1 : ℝ) (3 / 2 : ℝ) (13 / 8 : ℝ) (25 / 16 : ℝ) (1 / 16 : ℝ)
    (19 / 16 : ℝ) (41 / 16 : ℝ) (16 / 57 : ℝ) (16 / 41 : ℝ) (16 / 41 : ℝ) (1718502569263 / 10000000000000 : ℝ) (171850256927 / 1000000000000 : ℝ) (10468922707 / 1250000000000 : ℝ) (83751381763 / 10000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog_9 (by norm_num [quadLogLo]) (by norm_num [quadLogHi])

private lemma hlog_11 : (257920541247 / 1250000000000 : ℝ) ≤ Real.log (59 / 48 : ℝ) ∧ Real.log (59 / 48 : ℝ) ≤ (103168216499 / 500000000000 : ℝ) :=
  log_rat_bounds (59 / 48 : ℝ) (7 / 583 : ℝ) (1) (1) (-1) (257920541247 / 1250000000000 : ℝ) (103168216499 / 500000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hqsub_12 :
    IntervalIntegrable (fun t => Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t)) volume (13 / 8 : ℝ) (7 / 4 : ℝ) ∧
      (95904328019 / 10000000000000 : ℝ) ≤ ∫ t in (13 / 8 : ℝ)..(7 / 4 : ℝ), Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (13 / 8 : ℝ)..(7 / 4 : ℝ), Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t) ≤ (95904328097 / 10000000000000 : ℝ) :=
  quad_log_div_sub (2 / 3 : ℝ) (1 / 3 : ℝ) (1 : ℝ) (1 : ℝ) (13 / 8 : ℝ) (7 / 4 : ℝ) (27 / 16 : ℝ) (1 / 16 : ℝ)
    (59 / 48 : ℝ) (43 / 16 : ℝ) (16 / 59 : ℝ) (16 / 43 : ℝ) (16 / 43 : ℝ) (257920541247 / 1250000000000 : ℝ) (103168216499 / 500000000000 : ℝ) (95904328019 / 10000000000000 : ℝ) (95904328097 / 10000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog_11 (by norm_num [quadLogLo]) (by norm_num [quadLogHi])

private lemma hlog_13 : (47934570653 / 200000000000 : ℝ) ≤ Real.log (61 / 48 : ℝ) ∧ Real.log (61 / 48 : ℝ) ≤ (1198364266329 / 5000000000000 : ℝ) :=
  log_rat_bounds (61 / 48 : ℝ) (1 / 487 : ℝ) (-6) (4) (0) (47934570653 / 200000000000 : ℝ) (1198364266329 / 5000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hqsub_14 :
    IntervalIntegrable (fun t => Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t)) volume (7 / 4 : ℝ) (15 / 8 : ℝ) ∧
      (2661622601 / 250000000000 : ℝ) ≤ ∫ t in (7 / 4 : ℝ)..(15 / 8 : ℝ), Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (7 / 4 : ℝ)..(15 / 8 : ℝ), Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t) ≤ (106464904097 / 10000000000000 : ℝ) :=
  quad_log_div_sub (2 / 3 : ℝ) (1 / 3 : ℝ) (1 : ℝ) (1 : ℝ) (7 / 4 : ℝ) (15 / 8 : ℝ) (29 / 16 : ℝ) (1 / 16 : ℝ)
    (61 / 48 : ℝ) (45 / 16 : ℝ) (16 / 61 : ℝ) (16 / 45 : ℝ) (16 / 45 : ℝ) (47934570653 / 200000000000 : ℝ) (1198364266329 / 5000000000000 : ℝ) (2661622601 / 250000000000 : ℝ) (106464904097 / 10000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog_13 (by norm_num [quadLogLo]) (by norm_num [quadLogHi])

private lemma hlog_15 : (169958572177 / 625000000000 : ℝ) ≤ Real.log (21 / 16 : ℝ) ∧ Real.log (21 / 16 : ℝ) ≤ (2719337154841 / 10000000000000 : ℝ) :=
  log_rat_bounds (21 / 16 : ℝ) (1 / 251 : ℝ) (-5) (-1) (3) (169958572177 / 625000000000 : ℝ) (2719337154841 / 10000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hqsub_16 :
    IntervalIntegrable (fun t => Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t)) volume (15 / 8 : ℝ) (2 : ℝ) ∧
      (4626725843 / 400000000000 : ℝ) ≤ ∫ t in (15 / 8 : ℝ)..(2 : ℝ), Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (15 / 8 : ℝ)..(2 : ℝ), Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t) ≤ (57834073059 / 5000000000000 : ℝ) :=
  quad_log_div_sub (2 / 3 : ℝ) (1 / 3 : ℝ) (1 : ℝ) (1 : ℝ) (15 / 8 : ℝ) (2 : ℝ) (31 / 16 : ℝ) (1 / 16 : ℝ)
    (21 / 16 : ℝ) (47 / 16 : ℝ) (16 / 63 : ℝ) (16 / 47 : ℝ) (16 / 47 : ℝ) (169958572177 / 625000000000 : ℝ) (2719337154841 / 10000000000000 : ℝ) (4626725843 / 400000000000 : ℝ) (57834073059 / 5000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog_15 (by norm_num [quadLogLo]) (by norm_num [quadLogHi])

private lemma hlog_17 : (1515931294937 / 5000000000000 : ℝ) ≤ Real.log (65 / 48 : ℝ) ∧ Real.log (65 / 48 : ℝ) ≤ (3031862589881 / 10000000000000 : ℝ) :=
  log_rat_bounds (65 / 48 : ℝ) (1 / 649 : ℝ) (-2) (3) (-1) (1515931294937 / 5000000000000 : ℝ) (3031862589881 / 10000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hqsub_18 :
    IntervalIntegrable (fun t => Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t)) volume (2 : ℝ) (17 / 8 : ℝ) ∧
      (123707841791 / 10000000000000 : ℝ) ≤ ∫ t in (2 : ℝ)..(17 / 8 : ℝ), Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (2 : ℝ)..(17 / 8 : ℝ), Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t) ≤ (123707841823 / 10000000000000 : ℝ) :=
  quad_log_div_sub (2 / 3 : ℝ) (1 / 3 : ℝ) (1 : ℝ) (1 : ℝ) (2 : ℝ) (17 / 8 : ℝ) (33 / 16 : ℝ) (1 / 16 : ℝ)
    (65 / 48 : ℝ) (49 / 16 : ℝ) (16 / 65 : ℝ) (16 / 49 : ℝ) (16 / 49 : ℝ) (1515931294937 / 5000000000000 : ℝ) (3031862589881 / 10000000000000 : ℝ) (123707841791 / 10000000000000 : ℝ) (123707841823 / 10000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog_17 (by norm_num [quadLogLo]) (by norm_num [quadLogHi])

private lemma hlog_19 : (3334916084827 / 10000000000000 : ℝ) ≤ Real.log (67 / 48 : ℝ) ∧ Real.log (67 / 48 : ℝ) ≤ (1667458042417 / 5000000000000 : ℝ) :=
  log_rat_bounds (67 / 48 : ℝ) (1 / 401 : ℝ) (-1) (-2) (2) (3334916084827 / 10000000000000 : ℝ) (1667458042417 / 5000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hqsub_20 :
    IntervalIntegrable (fun t => Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t)) volume (17 / 8 : ℝ) (9 / 4 : ℝ) ∧
      (130744956887 / 10000000000000 : ℝ) ≤ ∫ t in (17 / 8 : ℝ)..(9 / 4 : ℝ), Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (17 / 8 : ℝ)..(9 / 4 : ℝ), Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t) ≤ (130744956911 / 10000000000000 : ℝ) :=
  quad_log_div_sub (2 / 3 : ℝ) (1 / 3 : ℝ) (1 : ℝ) (1 : ℝ) (17 / 8 : ℝ) (9 / 4 : ℝ) (35 / 16 : ℝ) (1 / 16 : ℝ)
    (67 / 48 : ℝ) (51 / 16 : ℝ) (16 / 67 : ℝ) (16 / 51 : ℝ) (16 / 51 : ℝ) (3334916084827 / 10000000000000 : ℝ) (1667458042417 / 5000000000000 : ℝ) (130744956887 / 10000000000000 : ℝ) (130744956911 / 10000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog_19 (by norm_num [quadLogLo]) (by norm_num [quadLogHi])

private lemma hlog_21 : (3629054936889 / 10000000000000 : ℝ) ≤ Real.log (23 / 16 : ℝ) ∧ Real.log (23 / 16 : ℝ) ≤ (1814527468449 / 5000000000000 : ℝ) :=
  log_rat_bounds (23 / 16 : ℝ) (11 / 2059 : ℝ) (6) (-2) (-1) (3629054936889 / 10000000000000 : ℝ) (1814527468449 / 5000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hqsub_22 :
    IntervalIntegrable (fun t => Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t)) volume (9 / 4 : ℝ) (19 / 8 : ℝ) ∧
      (5476564203 / 400000000000 : ℝ) ≤ ∫ t in (9 / 4 : ℝ)..(19 / 8 : ℝ), Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (9 / 4 : ℝ)..(19 / 8 : ℝ), Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t) ≤ (27382821019 / 2000000000000 : ℝ) :=
  quad_log_div_sub (2 / 3 : ℝ) (1 / 3 : ℝ) (1 : ℝ) (1 : ℝ) (9 / 4 : ℝ) (19 / 8 : ℝ) (37 / 16 : ℝ) (1 / 16 : ℝ)
    (23 / 16 : ℝ) (53 / 16 : ℝ) (16 / 69 : ℝ) (16 / 53 : ℝ) (16 / 53 : ℝ) (3629054936889 / 10000000000000 : ℝ) (1814527468449 / 5000000000000 : ℝ) (5476564203 / 400000000000 : ℝ) (27382821019 / 2000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog_21 (by norm_num [quadLogLo]) (by norm_num [quadLogHi])

private lemma hlog_23 : (391478866133 / 1000000000000 : ℝ) ≤ Real.log (71 / 48 : ℝ) ∧ Real.log (71 / 48 : ℝ) ≤ (1957394330669 / 5000000000000 : ℝ) :=
  log_rat_bounds (71 / 48 : ℝ) (47 / 3503 : ℝ) (2) (2) (-2) (391478866133 / 1000000000000 : ℝ) (1957394330669 / 5000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hqsub_24 :
    IntervalIntegrable (fun t => Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t)) volume (19 / 8 : ℝ) (5 / 2 : ℝ) ∧
      (142328567681 / 10000000000000 : ℝ) ≤ ∫ t in (19 / 8 : ℝ)..(5 / 2 : ℝ), Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (19 / 8 : ℝ)..(5 / 2 : ℝ), Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t) ≤ (8895535481 / 625000000000 : ℝ) :=
  quad_log_div_sub (2 / 3 : ℝ) (1 / 3 : ℝ) (1 : ℝ) (1 : ℝ) (19 / 8 : ℝ) (5 / 2 : ℝ) (39 / 16 : ℝ) (1 / 16 : ℝ)
    (71 / 48 : ℝ) (55 / 16 : ℝ) (16 / 71 : ℝ) (16 / 55 : ℝ) (16 / 55 : ℝ) (391478866133 / 1000000000000 : ℝ) (1957394330669 / 5000000000000 : ℝ) (142328567681 / 10000000000000 : ℝ) (8895535481 / 625000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog_23 (by norm_num [quadLogLo]) (by norm_num [quadLogHi])

private lemma hlog_25 : (1048146075601 / 2500000000000 : ℝ) ≤ Real.log (73 / 48 : ℝ) ∧ Real.log (73 / 48 : ℝ) ≤ (2096292151203 / 5000000000000 : ℝ) :=
  log_rat_bounds (73 / 48 : ℝ) (1 / 145 : ℝ) (-1) (1) (0) (1048146075601 / 2500000000000 : ℝ) (2096292151203 / 5000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hqsub_26 :
    IntervalIntegrable (fun t => Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t)) volume (5 / 2 : ℝ) (21 / 8 : ℝ) ∧
      (18385528183 / 1250000000000 : ℝ) ≤ ∫ t in (5 / 2 : ℝ)..(21 / 8 : ℝ), Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (5 / 2 : ℝ)..(21 / 8 : ℝ), Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t) ≤ (36771056369 / 2500000000000 : ℝ) :=
  quad_log_div_sub (2 / 3 : ℝ) (1 / 3 : ℝ) (1 : ℝ) (1 : ℝ) (5 / 2 : ℝ) (21 / 8 : ℝ) (41 / 16 : ℝ) (1 / 16 : ℝ)
    (73 / 48 : ℝ) (57 / 16 : ℝ) (16 / 73 : ℝ) (16 / 57 : ℝ) (16 / 57 : ℝ) (1048146075601 / 2500000000000 : ℝ) (2096292151203 / 5000000000000 : ℝ) (18385528183 / 1250000000000 : ℝ) (36771056369 / 2500000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog_25 (by norm_num [quadLogLo]) (by norm_num [quadLogHi])

private lemma hlog_27 : (4462871026281 / 10000000000000 : ℝ) ≤ Real.log (25 / 16 : ℝ) ∧ Real.log (25 / 16 : ℝ) ≤ (4462871026287 / 10000000000000 : ℝ) :=
  log_rat_bounds (25 / 16 : ℝ) (0 : ℝ) (-4) (0) (2) (4462871026281 / 10000000000000 : ℝ) (4462871026287 / 10000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hqsub_28 :
    IntervalIntegrable (fun t => Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t)) volume (21 / 8 : ℝ) (11 / 4 : ℝ) ∧
      (151262665749 / 10000000000000 : ℝ) ≤ ∫ t in (21 / 8 : ℝ)..(11 / 4 : ℝ), Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (21 / 8 : ℝ)..(11 / 4 : ℝ), Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t) ≤ (151262665759 / 10000000000000 : ℝ) :=
  quad_log_div_sub (2 / 3 : ℝ) (1 / 3 : ℝ) (1 : ℝ) (1 : ℝ) (21 / 8 : ℝ) (11 / 4 : ℝ) (43 / 16 : ℝ) (1 / 16 : ℝ)
    (25 / 16 : ℝ) (59 / 16 : ℝ) (16 / 75 : ℝ) (16 / 59 : ℝ) (16 / 59 : ℝ) (4462871026281 / 10000000000000 : ℝ) (4462871026287 / 10000000000000 : ℝ) (151262665749 / 10000000000000 : ℝ) (151262665759 / 10000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog_27 (by norm_num [quadLogLo]) (by norm_num [quadLogHi])

private lemma hlog_29 : (295377756841 / 625000000000 : ℝ) ≤ Real.log (77 / 48 : ℝ) ∧ Real.log (77 / 48 : ℝ) ≤ (236302205473 / 500000000000 : ℝ) :=
  log_rat_bounds (77 / 48 : ℝ) (1 / 769 : ℝ) (3) (0) (-1) (295377756841 / 625000000000 : ℝ) (236302205473 / 500000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hqsub_30 :
    IntervalIntegrable (fun t => Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t)) volume (11 / 4 : ℝ) (23 / 8 : ℝ) ∧
      (154933658017 / 10000000000000 : ℝ) ≤ ∫ t in (11 / 4 : ℝ)..(23 / 8 : ℝ), Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (11 / 4 : ℝ)..(23 / 8 : ℝ), Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t) ≤ (6197346321 / 400000000000 : ℝ) :=
  quad_log_div_sub (2 / 3 : ℝ) (1 / 3 : ℝ) (1 : ℝ) (1 : ℝ) (11 / 4 : ℝ) (23 / 8 : ℝ) (45 / 16 : ℝ) (1 / 16 : ℝ)
    (77 / 48 : ℝ) (61 / 16 : ℝ) (16 / 77 : ℝ) (16 / 61 : ℝ) (16 / 61 : ℝ) (295377756841 / 625000000000 : ℝ) (236302205473 / 500000000000 : ℝ) (154933658017 / 10000000000000 : ℝ) (6197346321 / 400000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog_29 (by norm_num [quadLogLo]) (by norm_num [quadLogHi])

private lemma hlog_31 : (4982468415587 / 10000000000000 : ℝ) ≤ Real.log (79 / 48 : ℝ) ∧ Real.log (79 / 48 : ℝ) ≤ (996493683119 / 2000000000000 : ℝ) :=
  log_rat_bounds (79 / 48 : ℝ) (31 / 3919 : ℝ) (-1) (4) (-2) (4982468415587 / 10000000000000 : ℝ) (996493683119 / 2000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hqsub_32 :
    IntervalIntegrable (fun t => Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t)) volume (23 / 8 : ℝ) (3 : ℝ) ∧
      (79078570679 / 5000000000000 : ℝ) ≤ ∫ t in (23 / 8 : ℝ)..(3 : ℝ), Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (23 / 8 : ℝ)..(3 : ℝ), Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t) ≤ (31631428273 / 2000000000000 : ℝ) :=
  quad_log_div_sub (2 / 3 : ℝ) (1 / 3 : ℝ) (1 : ℝ) (1 : ℝ) (23 / 8 : ℝ) (3 : ℝ) (47 / 16 : ℝ) (1 / 16 : ℝ)
    (79 / 48 : ℝ) (63 / 16 : ℝ) (16 / 79 : ℝ) (16 / 63 : ℝ) (16 / 63 : ℝ) (4982468415587 / 10000000000000 : ℝ) (996493683119 / 2000000000000 : ℝ) (79078570679 / 5000000000000 : ℝ) (31631428273 / 2000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog_31 (by norm_num [quadLogLo]) (by norm_num [quadLogHi])

private lemma hqchain_33 :
    IntervalIntegrable (fun t => Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t)) volume (1 : ℝ) (5 / 4 : ℝ) ∧
      (23420957953 / 5000000000000 : ℝ) ≤ ∫ t in (1 : ℝ)..(5 / 4 : ℝ), Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (1 : ℝ)..(5 / 4 : ℝ), Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t) ≤ (23420958347 / 5000000000000 : ℝ) :=
  chain_int_bounds hqsub_2 hqsub_4 (by norm_num) (by norm_num)

private lemma hqchain_34 :
    IntervalIntegrable (fun t => Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t)) volume (1 : ℝ) (11 / 8 : ℝ) ∧
      (100293595367 / 10000000000000 : ℝ) ≤ ∫ t in (1 : ℝ)..(11 / 8 : ℝ), Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (1 : ℝ)..(11 / 8 : ℝ), Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t) ≤ (10029359637 / 1000000000000 : ℝ) :=
  chain_int_bounds hqchain_33 hqsub_6 (by norm_num) (by norm_num)

private lemma hqchain_35 :
    IntervalIntegrable (fun t => Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t)) volume (1 : ℝ) (3 / 2 : ℝ) ∧
      (10625767163 / 625000000000 : ℝ) ≤ ∫ t in (1 : ℝ)..(3 / 2 : ℝ), Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (1 : ℝ)..(3 / 2 : ℝ), Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t) ≤ (85006137881 / 5000000000000 : ℝ) :=
  chain_int_bounds hqchain_34 hqsub_8 (by norm_num) (by norm_num)

private lemma hqchain_36 :
    IntervalIntegrable (fun t => Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t)) volume (1 : ℝ) (13 / 8 : ℝ) ∧
      (31720457033 / 1250000000000 : ℝ) ≤ ∫ t in (1 : ℝ)..(13 / 8 : ℝ), Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (1 : ℝ)..(13 / 8 : ℝ), Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t) ≤ (10150546301 / 400000000000 : ℝ) :=
  chain_int_bounds hqchain_35 hqsub_10 (by norm_num) (by norm_num)

private lemma hqchain_37 :
    IntervalIntegrable (fun t => Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t)) volume (1 : ℝ) (7 / 4 : ℝ) ∧
      (349667984283 / 10000000000000 : ℝ) ≤ ∫ t in (1 : ℝ)..(7 / 4 : ℝ), Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (1 : ℝ)..(7 / 4 : ℝ), Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t) ≤ (174833992811 / 5000000000000 : ℝ) :=
  chain_int_bounds hqchain_36 hqsub_12 (by norm_num) (by norm_num)

private lemma hqchain_38 :
    IntervalIntegrable (fun t => Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t)) volume (1 : ℝ) (15 / 8 : ℝ) ∧
      (456132888323 / 10000000000000 : ℝ) ≤ ∫ t in (1 : ℝ)..(15 / 8 : ℝ), Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (1 : ℝ)..(15 / 8 : ℝ), Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t) ≤ (456132889719 / 10000000000000 : ℝ) :=
  chain_int_bounds hqchain_37 hqsub_14 (by norm_num) (by norm_num)

private lemma hqchain_39 :
    IntervalIntegrable (fun t => Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t)) volume (1 : ℝ) (2 : ℝ) ∧
      (285900517199 / 5000000000000 : ℝ) ≤ ∫ t in (1 : ℝ)..(2 : ℝ), Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (1 : ℝ)..(2 : ℝ), Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t) ≤ (571801035837 / 10000000000000 : ℝ) :=
  chain_int_bounds hqchain_38 hqsub_16 (by norm_num) (by norm_num)

private lemma hqchain_40 :
    IntervalIntegrable (fun t => Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t)) volume (1 : ℝ) (17 / 8 : ℝ) ∧
      (695508876189 / 10000000000000 : ℝ) ≤ ∫ t in (1 : ℝ)..(17 / 8 : ℝ), Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (1 : ℝ)..(17 / 8 : ℝ), Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t) ≤ (34775443883 / 500000000000 : ℝ) :=
  chain_int_bounds hqchain_39 hqsub_18 (by norm_num) (by norm_num)

private lemma hqchain_41 :
    IntervalIntegrable (fun t => Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t)) volume (1 : ℝ) (9 / 4 : ℝ) ∧
      (206563458269 / 2500000000000 : ℝ) ≤ ∫ t in (1 : ℝ)..(9 / 4 : ℝ), Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (1 : ℝ)..(9 / 4 : ℝ), Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t) ≤ (826253834571 / 10000000000000 : ℝ) :=
  chain_int_bounds hqchain_40 hqsub_20 (by norm_num) (by norm_num)

private lemma hqchain_42 :
    IntervalIntegrable (fun t => Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t)) volume (1 : ℝ) (19 / 8 : ℝ) ∧
      (963167938151 / 10000000000000 : ℝ) ≤ ∫ t in (1 : ℝ)..(19 / 8 : ℝ), Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (1 : ℝ)..(19 / 8 : ℝ), Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t) ≤ (481583969833 / 5000000000000 : ℝ) :=
  chain_int_bounds hqchain_41 hqsub_22 (by norm_num) (by norm_num)

private lemma hqchain_43 :
    IntervalIntegrable (fun t => Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t)) volume (1 : ℝ) (5 / 2 : ℝ) ∧
      (138187063229 / 1250000000000 : ℝ) ≤ ∫ t in (1 : ℝ)..(5 / 2 : ℝ), Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (1 : ℝ)..(5 / 2 : ℝ), Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t) ≤ (552748253681 / 5000000000000 : ℝ) :=
  chain_int_bounds hqchain_42 hqsub_24 (by norm_num) (by norm_num)

private lemma hqchain_44 :
    IntervalIntegrable (fun t => Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t)) volume (1 : ℝ) (21 / 8 : ℝ) ∧
      (39143147853 / 312500000000 : ℝ) ≤ ∫ t in (1 : ℝ)..(21 / 8 : ℝ), Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (1 : ℝ)..(21 / 8 : ℝ), Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t) ≤ (626290366419 / 5000000000000 : ℝ) :=
  chain_int_bounds hqchain_43 hqsub_26 (by norm_num) (by norm_num)

private lemma hqchain_45 :
    IntervalIntegrable (fun t => Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t)) volume (1 : ℝ) (11 / 4 : ℝ) ∧
      (280768679409 / 2000000000000 : ℝ) ≤ ∫ t in (1 : ℝ)..(11 / 4 : ℝ), Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (1 : ℝ)..(11 / 4 : ℝ), Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t) ≤ (1403843398597 / 10000000000000 : ℝ) :=
  chain_int_bounds hqchain_44 hqsub_28 (by norm_num) (by norm_num)

private lemma hqchain_46 :
    IntervalIntegrable (fun t => Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t)) volume (1 : ℝ) (23 / 8 : ℝ) ∧
      (779388527531 / 5000000000000 : ℝ) ≤ ∫ t in (1 : ℝ)..(23 / 8 : ℝ), Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (1 : ℝ)..(23 / 8 : ℝ), Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t) ≤ (779388528311 / 5000000000000 : ℝ) :=
  chain_int_bounds hqchain_45 hqsub_30 (by norm_num) (by norm_num)

private lemma hqchain_47 :
    IntervalIntegrable (fun t => Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t)) volume (1 : ℝ) (3 : ℝ) ∧
      (85846709821 / 500000000000 : ℝ) ≤ ∫ t in (1 : ℝ)..(3 : ℝ), Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (1 : ℝ)..(3 : ℝ), Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t) ≤ (1716934197987 / 10000000000000 : ℝ) :=
  chain_int_bounds hqchain_46 hqsub_32 (by norm_num) (by norm_num)

private lemma hfga_48 : (0 : ℝ) ≤ ∫ s in (1 : ℝ)..(1 : ℝ), Real.log ((s + 2) / 3) / (s + 1) := by
  rw [integral_same]

private lemma hlog_49 : (7884573603639 / 10000000000000 : ℝ) ≤ Real.log (11 / 5 : ℝ) ∧ Real.log (11 / 5 : ℝ) ≤ (3942286801823 / 5000000000000 : ℝ) :=
  log_rat_bounds (11 / 5 : ℝ) (1 / 109 : ℝ) (1) (3) (-2) (7884573603639 / 10000000000000 : ℝ) (3942286801823 / 5000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hlog_50 : (7774075241773 / 10000000000000 : ℝ) ≤ Real.log (198 / 91 : ℝ) ∧ Real.log (198 / 91 : ℝ) ≤ (388703762089 / 500000000000 : ℝ) :=
  log_rat_bounds (198 / 91 : ℝ) (1 / 274 : ℝ) (1) (3) (-2) (7774075241773 / 10000000000000 : ℝ) (388703762089 / 500000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hlog_51 : (36968618813 / 10000000000000 : ℝ) ≤ Real.log (271 / 270 : ℝ) ∧ Real.log (271 / 270 : ℝ) ≤ (18484309407 / 5000000000000 : ℝ) :=
  log_rat_bounds (271 / 270 : ℝ) (1 / 541 : ℝ) (0) (0) (0) (36968618813 / 10000000000000 : ℝ) (18484309407 / 5000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hpsub_52 :
    IntervalIntegrable (fun t => Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1)) volume (1 : ℝ) (46 / 45 : ℝ) ∧
      (31530851 / 1000000000000 : ℝ) ≤ ∫ t in (1 : ℝ)..(46 / 45 : ℝ), Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1) :=
  quad_prod_log_div_sub (11 / 5 : ℝ) (198 / 91 : ℝ) (271 / 270 : ℝ) (1 : ℝ) (46 / 45 : ℝ) (91 / 90 : ℝ) (1 / 90 : ℝ)
    (90 / 91 : ℝ) (90 / 271 : ℝ) (90 / 181 : ℝ) (287396824236686851275449 / 100000000000000000000000000 : ℝ) (1613888952140526770006609338557 / 6376630000000000000000000000000 : ℝ) (-201422383465927030867199562297626799 / 406614101569000000000000000000000000 : ℝ) (599130838153573151807074304166771792878757 / 1270485562459086910300000000000000000000000 : ℝ)
    (7774075241773 / 10000000000000 : ℝ) (388703762089 / 500000000000 : ℝ) (36968618813 / 10000000000000 : ℝ) (18484309407 / 5000000000000 : ℝ) (31530851 / 1000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hlog_50 hlog_51 (by norm_num [quadProdLo])

private lemma hlog_53 : (472292210963 / 625000000000 : ℝ) ≤ Real.log (66 / 31 : ℝ) ∧ Real.log (66 / 31 : ℝ) ≤ (7556675375417 / 10000000000000 : ℝ) :=
  log_rat_bounds (66 / 31 : ℝ) (13 / 2803 : ℝ) (-6) (3) (1) (472292210963 / 625000000000 : ℝ) (7556675375417 / 10000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hlog_54 : (22099672373 / 2000000000000 : ℝ) ≤ Real.log (91 / 90 : ℝ) ∧ Real.log (91 / 90 : ℝ) ≤ (55249180933 / 5000000000000 : ℝ) :=
  log_rat_bounds (91 / 90 : ℝ) (1 / 181 : ℝ) (0) (0) (0) (22099672373 / 2000000000000 : ℝ) (55249180933 / 5000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hpsub_55 :
    IntervalIntegrable (fun t => Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1)) volume (46 / 45 : ℝ) (47 / 45 : ℝ) ∧
      (113806239 / 1250000000000 : ℝ) ≤ ∫ t in (46 / 45 : ℝ)..(47 / 45 : ℝ), Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1) :=
  quad_prod_log_div_sub (11 / 5 : ℝ) (66 / 31 : ℝ) (91 / 90 : ℝ) (46 / 45 : ℝ) (47 / 45 : ℝ) (31 / 30 : ℝ) (1 / 90 : ℝ)
    (30 / 31 : ℝ) (30 / 91 : ℝ) (30 / 61 : ℝ) (10437503126602098825199 / 1250000000000000000000000 : ℝ) (5040278684108533812642340863 / 21510125000000000000000000000 : ℝ) (-174030981952351051484329630723569 / 370148382012500000000000000000000 : ℝ) (2827291978721531476272003789813564447 / 6369550372509301250000000000000000000 : ℝ)
    (472292210963 / 625000000000 : ℝ) (7556675375417 / 10000000000000 : ℝ) (22099672373 / 2000000000000 : ℝ) (55249180933 / 5000000000000 : ℝ) (113806239 / 1250000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hlog_53 hlog_54 (by norm_num [quadProdLo])

private lemma hlog_56 : (7343901390937 / 10000000000000 : ℝ) ≤ Real.log (198 / 95 : ℝ) ∧ Real.log (198 / 95 : ℝ) ≤ (7343901390943 / 10000000000000 : ℝ) :=
  log_rat_bounds (198 / 95 : ℝ) (1 / 4751 : ℝ) (-2) (-1) (2) (7343901390937 / 10000000000000 : ℝ) (7343901390943 / 10000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hlog_57 : (91745693339 / 5000000000000 : ℝ) ≤ Real.log (55 / 54 : ℝ) ∧ Real.log (55 / 54 : ℝ) ≤ (91745693343 / 5000000000000 : ℝ) :=
  log_rat_bounds (55 / 54 : ℝ) (13 / 4387 : ℝ) (-4) (4) (-1) (91745693339 / 5000000000000 : ℝ) (91745693343 / 5000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hpsub_58 :
    IntervalIntegrable (fun t => Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1)) volume (47 / 45 : ℝ) (16 / 15 : ℝ) ∧
      (181851633 / 1250000000000 : ℝ) ≤ ∫ t in (47 / 45 : ℝ)..(16 / 15 : ℝ), Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1) :=
  quad_prod_log_div_sub (11 / 5 : ℝ) (198 / 95 : ℝ) (55 / 54 : ℝ) (47 / 45 : ℝ) (16 / 15 : ℝ) (19 / 18 : ℝ) (1 / 90 : ℝ)
    (18 / 19 : ℝ) (18 / 55 : ℝ) (18 / 37 : ℝ) (673771324924761555868643 / 50000000000000000000000000 : ℝ) (41836855491267352513411082517 / 193325000000000000000000000000 : ℝ) (-333696433841289554670026246214477 / 747491112500000000000000000000000 : ℝ) (1208550941715646434839511649129431237 / 2890174386481250000000000000000000000 : ℝ)
    (7343901390937 / 10000000000000 : ℝ) (7343901390943 / 10000000000000 : ℝ) (91745693339 / 5000000000000 : ℝ) (91745693343 / 5000000000000 : ℝ) (181851633 / 1250000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hlog_56 hlog_57 (by norm_num [quadProdLo])

private lemma hlog_59 : (7135560521907 / 10000000000000 : ℝ) ≤ Real.log (198 / 97 : ℝ) ∧ Real.log (198 / 97 : ℝ) ≤ (1427112104383 / 2000000000000 : ℝ) :=
  log_rat_bounds (198 / 97 : ℝ) (7 / 1753 : ℝ) (-3) (4) (-1) (7135560521907 / 10000000000000 : ℝ) (1427112104383 / 2000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hlog_60 : (51191094377 / 2000000000000 : ℝ) ≤ Real.log (277 / 270 : ℝ) ∧ Real.log (277 / 270 : ℝ) ≤ (127977735947 / 5000000000000 : ℝ) :=
  log_rat_bounds (277 / 270 : ℝ) (13 / 13837 : ℝ) (7) (0) (-3) (51191094377 / 2000000000000 : ℝ) (127977735947 / 5000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hpsub_61 :
    IntervalIntegrable (fun t => Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1)) volume (16 / 15 : ℝ) (49 / 45 : ℝ) ∧
      (975742041 / 5000000000000 : ℝ) ≤ ∫ t in (16 / 15 : ℝ)..(49 / 45 : ℝ), Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1) :=
  quad_prod_log_div_sub (11 / 5 : ℝ) (198 / 97 : ℝ) (277 / 270 : ℝ) (16 / 15 : ℝ) (49 / 45 : ℝ) (97 / 90 : ℝ) (1 / 90 : ℝ)
    (90 / 97 : ℝ) (90 / 277 : ℝ) (90 / 187 : ℝ) (365277152109736613016939 / 20000000000000000000000000 : ℝ) (20647369283879078623748771073 / 103598000000000000000000000000 : ℝ) (-22071979150624028479999551569643933 / 52052846179400000000000000000000000 : ℝ) (10311201175551926019806730844122865521993 / 26153968178693383820000000000000000000000 : ℝ)
    (7135560521907 / 10000000000000 : ℝ) (1427112104383 / 2000000000000 : ℝ) (51191094377 / 2000000000000 : ℝ) (127977735947 / 5000000000000 : ℝ) (975742041 / 5000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hlog_59 hlog_60 (by norm_num [quadProdLo])

private lemma hlog_62 : (3465735902799 / 5000000000000 : ℝ) ≤ Real.log (2 : ℝ) ∧ Real.log (2 : ℝ) ≤ (8664339757 / 12500000000 : ℝ) :=
  log_rat_bounds (2 : ℝ) (0 : ℝ) (1) (0) (0) (3465735902799 / 5000000000000 : ℝ) (8664339757 / 12500000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hlog_63 : (13115929129 / 400000000000 : ℝ) ≤ Real.log (31 / 30 : ℝ) ∧ Real.log (31 / 30 : ℝ) ≤ (65579645647 / 2000000000000 : ℝ) :=
  log_rat_bounds (31 / 30 : ℝ) (7 / 1543 : ℝ) (7) (0) (-3) (13115929129 / 400000000000 : ℝ) (65579645647 / 2000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hpsub_64 :
    IntervalIntegrable (fun t => Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1)) volume (49 / 45 : ℝ) (10 / 9 : ℝ) ∧
      (240334011 / 1000000000000 : ℝ) ≤ ∫ t in (49 / 45 : ℝ)..(10 / 9 : ℝ), Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1) :=
  quad_prod_log_div_sub (11 / 5 : ℝ) (2 : ℝ) (31 / 30 : ℝ) (49 / 45 : ℝ) (10 / 9 : ℝ) (11 / 10 : ℝ) (1 / 90 : ℝ)
    (10 / 11 : ℝ) (10 / 31 : ℝ) (10 / 21 : ℝ) (45456346480942516732071 / 2000000000000000000000000 : ℝ) (87347011317910400598121263 / 477400000000000000000000000 : ℝ) (-45912073286452833901319783561 / 113955380000000000000000000000 : ℝ) (30356130768615733822150046194301 / 81603447618000000000000000000000 : ℝ)
    (3465735902799 / 5000000000000 : ℝ) (8664339757 / 12500000000 : ℝ) (13115929129 / 400000000000 : ℝ) (65579645647 / 2000000000000 : ℝ) (240334011 / 1000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hlog_62 hlog_63 (by norm_num [quadProdLo])

private lemma hlog_65 : (210358285579 / 312500000000 : ℝ) ≤ Real.log (198 / 101 : ℝ) ∧ Real.log (198 / 101 : ℝ) ≤ (6731465138537 / 10000000000000 : ℝ) :=
  log_rat_bounds (198 / 101 : ℝ) (47 / 25297 : ℝ) (-6) (0) (3) (210358285579 / 312500000000 : ℝ) (6731465138537 / 10000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hlog_66 : (399327103349 / 10000000000000 : ℝ) ≤ Real.log (281 / 270 : ℝ) ∧ Real.log (281 / 270 : ℝ) ≤ (199663551679 / 5000000000000 : ℝ) :=
  log_rat_bounds (281 / 270 : ℝ) (113 / 13937 : ℝ) (7) (0) (-3) (399327103349 / 10000000000000 : ℝ) (199663551679 / 5000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hpsub_67 :
    IntervalIntegrable (fun t => Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1)) volume (10 / 9 : ℝ) (17 / 15 : ℝ) ∧
      (562613181 / 2000000000000 : ℝ) ≤ ∫ t in (10 / 9 : ℝ)..(17 / 15 : ℝ), Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1) :=
  quad_prod_log_div_sub (11 / 5 : ℝ) (198 / 101 : ℝ) (281 / 270 : ℝ) (10 / 9 : ℝ) (17 / 15 : ℝ) (101 / 90 : ℝ) (1 / 90 : ℝ)
    (90 / 101 : ℝ) (90 / 281 : ℝ) (90 / 191 : ℝ) (84001764845723789304071 / 3125000000000000000000000 : ℝ) (283487163585813874784350448541 / 1693990937500000000000000000000 : ℝ) (-351634530446724070344038569470379089 / 918273694826281250000000000000000000 : ℝ) (174846764464790154714251760013436960324181 / 497775141497715543784375000000000000000000 : ℝ)
    (210358285579 / 312500000000 : ℝ) (6731465138537 / 10000000000000 : ℝ) (399327103349 / 10000000000000 : ℝ) (199663551679 / 5000000000000 : ℝ) (562613181 / 2000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hlog_65 hlog_66 (by norm_num [quadProdLo])

private lemma hlog_68 : (1307076084929 / 2000000000000 : ℝ) ≤ Real.log (198 / 103 : ℝ) ∧ Real.log (198 / 103 : ℝ) ≤ (1633845106163 / 2500000000000 : ℝ) :=
  log_rat_bounds (198 / 103 : ℝ) (1 / 1649 : ℝ) (4) (1) (-2) (1307076084929 / 2000000000000 : ℝ) (1633845106163 / 2500000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hlog_69 : (94049877289 / 2000000000000 : ℝ) ≤ Real.log (283 / 270 : ℝ) ∧ Real.log (283 / 270 : ℝ) ≤ (117562346613 / 2500000000000 : ℝ) :=
  log_rat_bounds (283 / 270 : ℝ) (7 / 2257 : ℝ) (-3) (-1) (2) (94049877289 / 2000000000000 : ℝ) (117562346613 / 2500000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hpsub_70 :
    IntervalIntegrable (fun t => Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1)) volume (17 / 15 : ℝ) (52 / 45 : ℝ) ∧
      (397896111 / 1250000000000 : ℝ) ≤ ∫ t in (17 / 15 : ℝ)..(52 / 45 : ℝ), Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1) :=
  quad_prod_log_div_sub (11 / 5 : ℝ) (198 / 103 : ℝ) (283 / 270 : ℝ) (17 / 15 : ℝ) (52 / 45 : ℝ) (103 / 90 : ℝ) (1 / 90 : ℝ)
    (90 / 103 : ℝ) (90 / 283 : ℝ) (90 / 193 : ℝ) (122930345394958992277481 / 4000000000000000000000000 : ℝ) (342986524662543663006933356979 / 2250302800000000000000000000000 : ℝ) (-460881248756719424180661903803227839 / 1265965672921960000000000000000000000 : ℝ) (236384895281581323033840849185642594511099 / 712201524620042692372000000000000000000000 : ℝ)
    (1307076084929 / 2000000000000 : ℝ) (1633845106163 / 2500000000000 : ℝ) (94049877289 / 2000000000000 : ℝ) (117562346613 / 2500000000000 : ℝ) (397896111 / 1250000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hlog_68 hlog_69 (by norm_num [quadProdLo])

private lemma hlog_71 : (6343066805367 / 10000000000000 : ℝ) ≤ Real.log (66 / 35 : ℝ) ∧ Real.log (66 / 35 : ℝ) ≤ (1585766701343 / 2500000000000 : ℝ) :=
  log_rat_bounds (66 / 35 : ℝ) (1 / 351 : ℝ) (-3) (1) (1) (6343066805367 / 10000000000000 : ℝ) (1585766701343 / 2500000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hlog_72 : (270336106349 / 5000000000000 : ℝ) ≤ Real.log (19 / 18 : ℝ) ∧ Real.log (19 / 18 : ℝ) ≤ (135168053177 / 2500000000000 : ℝ) :=
  log_rat_bounds (19 / 18 : ℝ) (1 / 2431 : ℝ) (-7) (3) (1) (270336106349 / 5000000000000 : ℝ) (135168053177 / 2500000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hpsub_73 :
    IntervalIntegrable (fun t => Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1)) volume (52 / 45 : ℝ) (53 / 45 : ℝ) ∧
      (3515992799 / 10000000000000 : ℝ) ≤ ∫ t in (52 / 45 : ℝ)..(53 / 45 : ℝ), Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1) :=
  quad_prod_log_div_sub (11 / 5 : ℝ) (66 / 35 : ℝ) (19 / 18 : ℝ) (52 / 45 : ℝ) (53 / 45 : ℝ) (7 / 6 : ℝ) (1 / 90 : ℝ)
    (6 / 7 : ℝ) (6 / 19 : ℝ) (6 / 13 : ℝ) (1714759982474504995975083 / 50000000000000000000000000 : ℝ) (5970906408272537506605941883 / 43225000000000000000000000000 : ℝ) (-12936715623692658977635770811317 / 37368012500000000000000000000000 : ℝ) (10138336931217563917711672553715483 / 32304646806250000000000000000000000 : ℝ)
    (6343066805367 / 10000000000000 : ℝ) (1585766701343 / 2500000000000 : ℝ) (270336106349 / 5000000000000 : ℝ) (135168053177 / 2500000000000 : ℝ) (3515992799 / 10000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hlog_71 hlog_72 (by norm_num [quadProdLo])

private lemma hlog_74 : (1538595490581 / 2500000000000 : ℝ) ≤ Real.log (198 / 107 : ℝ) ∧ Real.log (198 / 107 : ℝ) ≤ (769297745291 / 1250000000000 : ℝ) :=
  log_rat_bounds (198 / 107 : ℝ) (3 / 217 : ℝ) (0) (2) (-1) (1538595490581 / 2500000000000 : ℝ) (769297745291 / 1250000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hlog_75 : (76325320951 / 1250000000000 : ℝ) ≤ Real.log (287 / 270 : ℝ) ∧ Real.log (287 / 270 : ℝ) ≤ (610602567617 / 10000000000000 : ℝ) :=
  log_rat_bounds (287 / 270 : ℝ) (143 / 36593 : ℝ) (-7) (3) (1) (76325320951 / 1250000000000 : ℝ) (610602567617 / 10000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hpsub_76 :
    IntervalIntegrable (fun t => Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1)) volume (53 / 45 : ℝ) (6 / 5 : ℝ) ∧
      (1906865069 / 5000000000000 : ℝ) ≤ ∫ t in (53 / 45 : ℝ)..(6 / 5 : ℝ), Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1) :=
  quad_prod_log_div_sub (11 / 5 : ℝ) (198 / 107 : ℝ) (287 / 270 : ℝ) (53 / 45 : ℝ) (6 / 5 : ℝ) (107 / 90 : ℝ) (1 / 90 : ℝ)
    (90 / 107 : ℝ) (90 / 287 : ℝ) (90 / 197 : ℝ) (117433794632356122462531 / 3125000000000000000000000 : ℝ) (235308602069636643767683219689 / 1890522812500000000000000000000 : ℝ) (-376611006420038545049530430940865509 / 1143704481466531250000000000000000000 : ℝ) (205452827635408906999485002287617350242929 / 691903812150707450678125000000000000000000 : ℝ)
    (1538595490581 / 2500000000000 : ℝ) (769297745291 / 1250000000000 : ℝ) (76325320951 / 1250000000000 : ℝ) (610602567617 / 10000000000000 : ℝ) (1906865069 / 5000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hlog_74 hlog_75 (by norm_num [quadProdLo])

private lemma hlog_77 : (5969191484651 / 10000000000000 : ℝ) ≤ Real.log (198 / 109 : ℝ) ∧ Real.log (198 / 109 : ℝ) ≤ (373074467791 / 625000000000 : ℝ) :=
  log_rat_bounds (198 / 109 : ℝ) (1 / 219 : ℝ) (0) (2) (-1) (5969191484651 / 10000000000000 : ℝ) (373074467791 / 625000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hlog_78 : (340023645569 / 5000000000000 : ℝ) ≤ Real.log (289 / 270 : ℝ) ∧ Real.log (289 / 270 : ℝ) ≤ (680047291143 / 10000000000000 : ℝ) :=
  log_rat_bounds (289 / 270 : ℝ) (1 / 577 : ℝ) (4) (-1) (-1) (340023645569 / 5000000000000 : ℝ) (680047291143 / 10000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hpsub_79 :
    IntervalIntegrable (fun t => Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1)) volume (6 / 5 : ℝ) (11 / 9 : ℝ) ∧
      (509804187 / 1250000000000 : ℝ) ≤ ∫ t in (6 / 5 : ℝ)..(11 / 9 : ℝ), Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1) :=
  quad_prod_log_div_sub (11 / 5 : ℝ) (198 / 109 : ℝ) (289 / 270 : ℝ) (6 / 5 : ℝ) (11 / 9 : ℝ) (109 / 90 : ℝ) (1 / 90 : ℝ)
    (90 / 109 : ℝ) (90 / 289 : ℝ) (90 / 199 : ℝ) (2029666249710464527661419 / 50000000000000000000000000 : ℝ) (3491110324192565447227238760729 / 31343495000000000000000000000000 : ℝ) (-6155264202360997897735629733815518061 / 19648293576300500000000000000000000000 : ℝ) (3462590384721668108395837629449303709956049 / 12316923829346136804950000000000000000000000 : ℝ)
    (5969191484651 / 10000000000000 : ℝ) (373074467791 / 625000000000 : ℝ) (340023645569 / 5000000000000 : ℝ) (680047291143 / 10000000000000 : ℝ) (509804187 / 1250000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hlog_77 hlog_78 (by norm_num [quadProdLo])

private lemma hlog_80 : (5787368293819 / 10000000000000 : ℝ) ≤ Real.log (66 / 37 : ℝ) ∧ Real.log (66 / 37 : ℝ) ≤ (90427629591 / 156250000000 : ℝ) :=
  log_rat_bounds (66 / 37 : ℝ) (1 / 593 : ℝ) (4) (-2) (0) (5787368293819 / 10000000000000 : ℝ) (90427629591 / 156250000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hlog_81 : (5851664701 / 78125000000 : ℝ) ≤ Real.log (97 / 90 : ℝ) ∧ Real.log (97 / 90 : ℝ) ≤ (374506540867 / 5000000000000 : ℝ) :=
  log_rat_bounds (97 / 90 : ℝ) (1 / 193 : ℝ) (4) (-1) (-1) (5851664701 / 78125000000 : ℝ) (374506540867 / 5000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hpsub_82 :
    IntervalIntegrable (fun t => Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1)) volume (11 / 9 : ℝ) (56 / 45 : ℝ) ∧
      (862405179 / 2000000000000 : ℝ) ≤ ∫ t in (11 / 9 : ℝ)..(56 / 45 : ℝ), Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1) :=
  quad_prod_log_div_sub (11 / 5 : ℝ) (66 / 37 : ℝ) (97 / 90 : ℝ) (11 / 9 : ℝ) (56 / 45 : ℝ) (37 / 30 : ℝ) (1 / 90 : ℝ)
    (30 / 37 : ℝ) (30 / 97 : ℝ) (30 / 67 : ℝ) (33865738756627238783119 / 781250000000000000000000 : ℝ) (1857019930391854441897157727 / 18786171875000000000000000000 : ℝ) (-134656742848997471895398884746609 / 451737924757812500000000000000000 : ℝ) (2892827830159324578318402057691739103 / 10862625660103786718750000000000000000 : ℝ)
    (5787368293819 / 10000000000000 : ℝ) (90427629591 / 156250000000 : ℝ) (5851664701 / 78125000000 : ℝ) (374506540867 / 5000000000000 : ℝ) (862405179 / 2000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hlog_80 hlog_81 (by norm_num [quadProdLo])

private lemma hlog_83 : (5608792119817 / 10000000000000 : ℝ) ≤ Real.log (198 / 113 : ℝ) ∧ Real.log (198 / 113 : ℝ) ≤ (2804396059913 / 5000000000000 : ℝ) :=
  log_rat_bounds (198 / 113 : ℝ) (131 / 28381 : ℝ) (-3) (-2) (3) (5608792119817 / 10000000000000 : ℝ) (2804396059913 / 5000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hlog_84 : (102188312523 / 1250000000000 : ℝ) ≤ Real.log (293 / 270 : ℝ) ∧ Real.log (293 / 270 : ℝ) ≤ (81750650019 / 1000000000000 : ℝ) :=
  log_rat_bounds (293 / 270 : ℝ) (7 / 2923 : ℝ) (0) (3) (-2) (102188312523 / 1250000000000 : ℝ) (81750650019 / 1000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hpsub_85 :
    IntervalIntegrable (fun t => Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1)) volume (56 / 45 : ℝ) (19 / 15 : ℝ) ∧
      (4516310239 / 10000000000000 : ℝ) ≤ ∫ t in (56 / 45 : ℝ)..(19 / 15 : ℝ), Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1) :=
  quad_prod_log_div_sub (11 / 5 : ℝ) (198 / 113 : ℝ) (293 / 270 : ℝ) (56 / 45 : ℝ) (19 / 15 : ℝ) (113 / 90 : ℝ) (1 / 90 : ℝ)
    (90 / 113 : ℝ) (90 / 293 : ℝ) (90 / 203 : ℝ) (573153002016399257568291 / 12500000000000000000000000 : ℝ) (729611945066579136580543079529 / 8401408750000000000000000000000 : ℝ) (-1601851078633240428525502432381130949 / 5646693518766125000000000000000000000 : ℝ) (957984989713197741389519468954611781313969 / 3795214426970400942287500000000000000000000 : ℝ)
    (5608792119817 / 10000000000000 : ℝ) (2804396059913 / 5000000000000 : ℝ) (102188312523 / 1250000000000 : ℝ) (81750650019 / 1000000000000 : ℝ) (4516310239 / 10000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hlog_83 hlog_84 (by norm_num [quadProdLo])

private lemma hlog_86 : (1358337255827 / 2500000000000 : ℝ) ≤ Real.log (198 / 115 : ℝ) ∧ Real.log (198 / 115 : ℝ) ≤ (5433349023317 / 10000000000000 : ℝ) :=
  log_rat_bounds (198 / 115 : ℝ) (13 / 2957 : ℝ) (7) (-1) (-2) (1358337255827 / 2500000000000 : ℝ) (5433349023317 / 10000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hlog_87 : (885533973411 / 10000000000000 : ℝ) ≤ Real.log (59 / 54 : ℝ) ∧ Real.log (59 / 54 : ℝ) ≤ (442766986709 / 5000000000000 : ℝ) :=
  log_rat_bounds (59 / 54 : ℝ) (17 / 2933 : ℝ) (0) (3) (-2) (885533973411 / 10000000000000 : ℝ) (442766986709 / 5000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hpsub_88 :
    IntervalIntegrable (fun t => Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1)) volume (19 / 15 : ℝ) (58 / 45 : ℝ) ∧
      (4692977969 / 10000000000000 : ℝ) ≤ ∫ t in (19 / 15 : ℝ)..(58 / 45 : ℝ), Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1) :=
  quad_prod_log_div_sub (11 / 5 : ℝ) (198 / 115 : ℝ) (59 / 54 : ℝ) (19 / 15 : ℝ) (58 / 45 : ℝ) (23 / 18 : ℝ) (1 / 90 : ℝ)
    (18 / 23 : ℝ) (18 / 59 : ℝ) (18 / 41 : ℝ) (1202853787384677322815897 / 25000000000000000000000000 : ℝ) (888037784048834294177109321 / 11787500000000000000000000000 : ℝ) (-88537277361967702658535036137373 / 327910568750000000000000000000000 : ℝ) (2183642951158560895493035896345736449 / 9121980156771875000000000000000000000 : ℝ)
    (1358337255827 / 2500000000000 : ℝ) (5433349023317 / 10000000000000 : ℝ) (885533973411 / 10000000000000 : ℝ) (442766986709 / 5000000000000 : ℝ) (4692977969 / 10000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hlog_86 hlog_87 (by norm_num [quadProdLo])

private lemma hlog_89 : (1315232739741 / 2500000000000 : ℝ) ≤ Real.log (22 / 13 : ℝ) ∧ Real.log (22 / 13 : ℝ) ≤ (5260930958971 / 10000000000000 : ℝ) :=
  log_rat_bounds (22 / 13 : ℝ) (1 / 703 : ℝ) (-4) (3) (0) (1315232739741 / 2500000000000 : ℝ) (5260930958971 / 10000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hlog_90 : (23827544951 / 250000000000 : ℝ) ≤ Real.log (11 / 10 : ℝ) ∧ Real.log (11 / 10 : ℝ) ≤ (953101798047 / 10000000000000 : ℝ) :=
  log_rat_bounds (11 / 10 : ℝ) (1 / 109 : ℝ) (0) (3) (-2) (23827544951 / 250000000000 : ℝ) (953101798047 / 10000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hpsub_91 :
    IntervalIntegrable (fun t => Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1)) volume (58 / 45 : ℝ) (59 / 45 : ℝ) ∧
      (1210904247 / 2500000000000 : ℝ) ≤ ∫ t in (58 / 45 : ℝ)..(59 / 45 : ℝ), Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1) :=
  quad_prod_log_div_sub (11 / 5 : ℝ) (22 / 13 : ℝ) (11 / 10 : ℝ) (58 / 45 : ℝ) (59 / 45 : ℝ) (13 / 10 : ℝ) (1 / 90 : ℝ)
    (10 / 13 : ℝ) (10 / 33 : ℝ) (10 / 23 : ℝ) (31338767227205561597691 / 625000000000000000000000 : ℝ) (13218849870215354691530187 / 205562500000000000000000000 : ℝ) (-52130143383339671787666450223 / 202828518750000000000000000000 : ℝ) (136371570198738965246476721437001 / 600392698351875000000000000000000 : ℝ)
    (1315232739741 / 2500000000000 : ℝ) (5260930958971 / 10000000000000 : ℝ) (23827544951 / 250000000000 : ℝ) (953101798047 / 10000000000000 : ℝ) (1210904247 / 2500000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hlog_89 hlog_90 (by norm_num [quadProdLo])

private lemma hlog_92 : (203657415033 / 400000000000 : ℝ) ≤ Real.log (198 / 119 : ℝ) ∧ Real.log (198 / 119 : ℝ) ≤ (2545717687917 / 5000000000000 : ℝ) :=
  log_rat_bounds (198 / 119 : ℝ) (29 / 2171 : ℝ) (-1) (4) (-2) (203657415033 / 400000000000 : ℝ) (2545717687917 / 5000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hlog_93 : (12752701799 / 125000000000 : ℝ) ≤ Real.log (299 / 270 : ℝ) ∧ Real.log (299 / 270 : ℝ) ≤ (510108071963 / 5000000000000 : ℝ) :=
  log_rat_bounds (299 / 270 : ℝ) (37 / 2953 : ℝ) (0) (3) (-2) (12752701799 / 125000000000 : ℝ) (510108071963 / 5000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hpsub_94 :
    IntervalIntegrable (fun t => Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1)) volume (59 / 45 : ℝ) (4 / 3 : ℝ) ∧
      (2484859467 / 5000000000000 : ℝ) ≤ ∫ t in (59 / 45 : ℝ)..(4 / 3 : ℝ), Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1) :=
  quad_prod_log_div_sub (11 / 5 : ℝ) (198 / 119 : ℝ) (299 / 270 : ℝ) (59 / 45 : ℝ) (4 / 3 : ℝ) (119 / 90 : ℝ) (1 / 90 : ℝ)
    (90 / 119 : ℝ) (90 / 299 : ℝ) (90 / 209 : ℝ) (2597182283071028744367 / 50000000000000000000000 : ℝ) (1997671212884196011220099957 / 37182145000000000000000000000 : ℝ) (-6765254968273176106728763889130153 / 27650238136020500000000000000000000 : ℝ) (4433679294879082648393845426277259765037 / 20561903273160879079450000000000000000000 : ℝ)
    (203657415033 / 400000000000 : ℝ) (2545717687917 / 5000000000000 : ℝ) (12752701799 / 125000000000 : ℝ) (510108071963 / 5000000000000 : ℝ) (2484859467 / 5000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hlog_92 hlog_93 (by norm_num [quadProdLo])

private lemma hlog_95 : (2462382425487 / 5000000000000 : ℝ) ≤ Real.log (18 / 11 : ℝ) ∧ Real.log (18 / 11 : ℝ) ≤ (2462382425491 / 5000000000000 : ℝ) :=
  log_rat_bounds (18 / 11 : ℝ) (1 / 199 : ℝ) (-1) (4) (-2) (2462382425487 / 5000000000000 : ℝ) (2462382425491 / 5000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hlog_96 : (543441528751 / 5000000000000 : ℝ) ≤ Real.log (301 / 270 : ℝ) ∧ Real.log (301 / 270 : ℝ) ≤ (1086883057507 / 10000000000000 : ℝ) :=
  log_rat_bounds (301 / 270 : ℝ) (1 / 601 : ℝ) (1) (-2) (1) (543441528751 / 5000000000000 : ℝ) (1086883057507 / 10000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hpsub_97 :
    IntervalIntegrable (fun t => Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1)) volume (4 / 3 : ℝ) (61 / 45 : ℝ) ∧
      (634085733 / 1250000000000 : ℝ) ≤ ∫ t in (4 / 3 : ℝ)..(61 / 45 : ℝ), Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1) :=
  quad_prod_log_div_sub (11 / 5 : ℝ) (18 / 11 : ℝ) (301 / 270 : ℝ) (4 / 3 : ℝ) (61 / 45 : ℝ) (121 / 90 : ℝ) (1 / 90 : ℝ)
    (90 / 121 : ℝ) (90 / 301 : ℝ) (90 / 211 : ℝ) (1338160869676250625676737 / 25000000000000000000000000 : ℝ) (76111933768805827605458914137 / 1746552500000000000000000000000 : ℝ) (-312645957157680419526105772006053093 / 1342196079512750000000000000000000000 : ℝ) (211237768925152027414082789240092137301377 / 1031455003991804609525000000000000000000000 : ℝ)
    (2462382425487 / 5000000000000 : ℝ) (2462382425491 / 5000000000000 : ℝ) (543441528751 / 5000000000000 : ℝ) (1086883057507 / 10000000000000 : ℝ) (634085733 / 1250000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hlog_95 hlog_96 (by norm_num [quadProdLo])

private lemma hlog_98 : (4760826753219 / 10000000000000 : ℝ) ≤ Real.log (66 / 41 : ℝ) ∧ Real.log (66 / 41 : ℝ) ≤ (4760826753223 / 10000000000000 : ℝ) :=
  log_rat_bounds (66 / 41 : ℝ) (1 / 329 : ℝ) (3) (0) (-1) (4760826753219 / 10000000000000 : ℝ) (4760826753223 / 10000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hlog_99 : (1153108465107 / 10000000000000 : ℝ) ≤ Real.log (101 / 90 : ℝ) ∧ Real.log (101 / 90 : ℝ) ≤ (144138558139 / 1250000000000 : ℝ) :=
  log_rat_bounds (101 / 90 : ℝ) (1 / 201 : ℝ) (1) (-2) (1) (1153108465107 / 10000000000000 : ℝ) (144138558139 / 1250000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hpsub_100 :
    IntervalIntegrable (fun t => Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1)) volume (61 / 45 : ℝ) (62 / 45 : ℝ) ∧
      (2576918201 / 5000000000000 : ℝ) ≤ ∫ t in (61 / 45 : ℝ)..(62 / 45 : ℝ), Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1) :=
  quad_prod_log_div_sub (11 / 5 : ℝ) (66 / 41 : ℝ) (101 / 90 : ℝ) (61 / 45 : ℝ) (62 / 45 : ℝ) (41 / 30 : ℝ) (1 / 90 : ℝ)
    (30 / 41 : ℝ) (30 / 101 : ℝ) (30 / 71 : ℝ) (5489749630044703361429433 / 100000000000000000000000000 : ℝ) (99495616606101010140962153841 / 2940110000000000000000000000000 : ℝ) (-19170420233648305595021172837166743 / 86442468121000000000000000000000000 : ℝ) (494574524561825809339257110156122448289 / 2541503649472333100000000000000000000000 : ℝ)
    (4760826753219 / 10000000000000 : ℝ) (4760826753223 / 10000000000000 : ℝ) (1153108465107 / 10000000000000 : ℝ) (144138558139 / 1250000000000 : ℝ) (2576918201 / 5000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hlog_98 hlog_99 (by norm_num [quadProdLo])

private lemma hlog_101 : (4599532933917 / 10000000000000 : ℝ) ≤ Real.log (198 / 125 : ℝ) ∧ Real.log (198 / 125 : ℝ) ≤ (4599532933927 / 10000000000000 : ℝ) :=
  log_rat_bounds (198 / 125 : ℝ) (19 / 16019 : ℝ) (7) (-4) (0) (4599532933917 / 10000000000000 : ℝ) (4599532933927 / 10000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hlog_102 : (152362272011 / 1250000000000 : ℝ) ≤ Real.log (61 / 54 : ℝ) ∧ Real.log (61 / 54 : ℝ) ≤ (1218898176093 / 10000000000000 : ℝ) :=
  log_rat_bounds (61 / 54 : ℝ) (1 / 487 : ℝ) (-3) (2) (0) (152362272011 / 1250000000000 : ℝ) (1218898176093 / 10000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hpsub_103 :
    IntervalIntegrable (fun t => Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1)) volume (62 / 45 : ℝ) (7 / 5 : ℝ) ∧
      (5214411397 / 10000000000000 : ℝ) ≤ ∫ t in (62 / 45 : ℝ)..(7 / 5 : ℝ), Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1) :=
  quad_prod_log_div_sub (11 / 5 : ℝ) (198 / 125 : ℝ) (61 / 54 : ℝ) (62 / 45 : ℝ) (7 / 5 : ℝ) (25 / 18 : ℝ) (1 / 90 : ℝ)
    (18 / 25 : ℝ) (18 / 61 : ℝ) (18 / 43 : ℝ) (700795288001014841697087 / 12500000000000000000000000 : ℝ) (401560981524320801908299237 / 16393750000000000000000000000 : ℝ) (-4539673322006874019860656281113 / 21500403125000000000000000000000 : ℝ) (5216353221240662539977276058331037 / 28197778698437500000000000000000000 : ℝ)
    (4599532933917 / 10000000000000 : ℝ) (4599532933927 / 10000000000000 : ℝ) (152362272011 / 1250000000000 : ℝ) (1218898176093 / 10000000000000 : ℝ) (5214411397 / 10000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hlog_101 hlog_102 (by norm_num [quadProdLo])

private lemma hlog_104 : (888159888471 / 2000000000000 : ℝ) ≤ Real.log (198 / 127 : ℝ) ∧ Real.log (198 / 127 : ℝ) ≤ (1110199860591 / 2500000000000 : ℝ) :=
  log_rat_bounds (198 / 127 : ℝ) (163 / 31913 : ℝ) (0) (-4) (3) (888159888471 / 2000000000000 : ℝ) (1110199860591 / 2500000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hlog_105 : (642128942943 / 5000000000000 : ℝ) ≤ Real.log (307 / 270 : ℝ) ∧ Real.log (307 / 270 : ℝ) ≤ (1284257885891 / 10000000000000 : ℝ) :=
  log_rat_bounds (307 / 270 : ℝ) (13 / 2443 : ℝ) (-3) (2) (0) (642128942943 / 5000000000000 : ℝ) (1284257885891 / 10000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hpsub_106 :
    IntervalIntegrable (fun t => Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1)) volume (7 / 5 : ℝ) (64 / 45 : ℝ) ∧
      (5255579141 / 10000000000000 : ℝ) ≤ ∫ t in (7 / 5 : ℝ)..(64 / 45 : ℝ), Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1) :=
  quad_prod_log_div_sub (11 / 5 : ℝ) (198 / 127 : ℝ) (307 / 270 : ℝ) (7 / 5 : ℝ) (64 / 45 : ℝ) (127 / 90 : ℝ) (1 / 90 : ℝ)
    (90 / 127 : ℝ) (90 / 307 : ℝ) (90 / 217 : ℝ) (570313170348256002510153 / 10000000000000000000000000 : ℝ) (1034084092912005665064447261 / 66619000000000000000000000000 : ℝ) (-11330448424204334483490279608332161 / 56363757744700000000000000000000000 : ℝ) (8389742535033327604717626443843363627061 / 47687194150365950110000000000000000000000 : ℝ)
    (888159888471 / 2000000000000 : ℝ) (1110199860591 / 2500000000000 : ℝ) (642128942943 / 5000000000000 : ℝ) (1284257885891 / 10000000000000 : ℝ) (5255579141 / 10000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hlog_104 hlog_105 (by norm_num [quadProdLo])

private lemma hlog_107 : (4284546263327 / 10000000000000 : ℝ) ≤ Real.log (66 / 43 : ℝ) ∧ Real.log (66 / 43 : ℝ) ≤ (428454626333 / 1000000000000 : ℝ) :=
  log_rat_bounds (66 / 43 : ℝ) (1 / 87 : ℝ) (-1) (1) (0) (4284546263327 / 10000000000000 : ℝ) (428454626333 / 1000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hlog_108 : (1349193178991 / 10000000000000 : ℝ) ≤ Real.log (103 / 90 : ℝ) ∧ Real.log (103 / 90 : ℝ) ≤ (337298294749 / 2500000000000 : ℝ) :=
  log_rat_bounds (103 / 90 : ℝ) (7 / 817 : ℝ) (-3) (2) (0) (1349193178991 / 10000000000000 : ℝ) (337298294749 / 2500000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hpsub_109 :
    IntervalIntegrable (fun t => Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1)) volume (64 / 45 : ℝ) (13 / 9 : ℝ) ∧
      (5278440183 / 10000000000000 : ℝ) ≤ ∫ t in (64 / 45 : ℝ)..(13 / 9 : ℝ), Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1) :=
  quad_prod_log_div_sub (11 / 5 : ℝ) (66 / 43 : ℝ) (103 / 90 : ℝ) (64 / 45 : ℝ) (13 / 9 : ℝ) (43 / 30 : ℝ) (1 / 90 : ℝ)
    (30 / 43 : ℝ) (30 / 103 : ℝ) (30 / 73 : ℝ) (5780680593552165330163057 / 100000000000000000000000000 : ℝ) (22330313185976099258123461641 / 3233170000000000000000000000000 : ℝ) (-20005924652053359050562686434823967 / 104533882489000000000000000000000000 : ℝ) (565722641406203453071384374659506049529 / 3379758128469601300000000000000000000000 : ℝ)
    (4284546263327 / 10000000000000 : ℝ) (428454626333 / 1000000000000 : ℝ) (1349193178991 / 10000000000000 : ℝ) (337298294749 / 2500000000000 : ℝ) (5278440183 / 10000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hlog_107 hlog_108 (by norm_num [quadProdLo])

private lemma hlog_110 : (1032674268733 / 2500000000000 : ℝ) ≤ Real.log (198 / 131 : ℝ) ∧ Real.log (198 / 131 : ℝ) ≤ (826139414987 / 2000000000000 : ℝ) :=
  log_rat_bounds (198 / 131 : ℝ) (1 / 263 : ℝ) (-1) (1) (0) (1032674268733 / 2500000000000 : ℝ) (826139414987 / 2000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hlog_111 : (706854765903 / 5000000000000 : ℝ) ≤ Real.log (311 / 270 : ℝ) ∧ Real.log (311 / 270 : ℝ) ≤ (1413709531811 / 10000000000000 : ℝ) :=
  log_rat_bounds (311 / 270 : ℝ) (29 / 2459 : ℝ) (-3) (2) (0) (706854765903 / 5000000000000 : ℝ) (1413709531811 / 10000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hpsub_112 :
    IntervalIntegrable (fun t => Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1)) volume (13 / 9 : ℝ) (22 / 15 : ℝ) ∧
      (165125993 / 312500000000 : ℝ) ≤ ∫ t in (13 / 9 : ℝ)..(22 / 15 : ℝ), Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1) :=
  quad_prod_log_div_sub (11 / 5 : ℝ) (198 / 131 : ℝ) (311 / 270 : ℝ) (13 / 9 : ℝ) (22 / 15 : ℝ) (131 / 90 : ℝ) (1 / 90 : ℝ)
    (90 / 131 : ℝ) (90 / 311 : ℝ) (90 / 221 : ℝ) (729950728479316427410899 / 12500000000000000000000000 : ℝ) (-1184708870811794817102071187 / 865746250000000000000000000000 : ℝ) (-142018577606723571369046750659933897 / 779497232164625000000000000000000000 : ℝ) (111814152026680229736089923075227302079093 / 701840677857179615462500000000000000000000 : ℝ)
    (1032674268733 / 2500000000000 : ℝ) (826139414987 / 2000000000000 : ℝ) (706854765903 / 5000000000000 : ℝ) (1413709531811 / 10000000000000 : ℝ) (165125993 / 312500000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hlog_110 hlog_111 (by norm_num [quadProdLo])

private lemma hlog_113 : (994794756181 / 2500000000000 : ℝ) ≤ Real.log (198 / 133 : ℝ) ∧ Real.log (198 / 133 : ℝ) ≤ (3979179024731 / 10000000000000 : ℝ) :=
  log_rat_bounds (198 / 133 : ℝ) (13 / 5333 : ℝ) (3) (-3) (1) (994794756181 / 2500000000000 : ℝ) (3979179024731 / 10000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hlog_114 : (1477812315413 / 10000000000000 : ℝ) ≤ Real.log (313 / 270 : ℝ) ∧ Real.log (313 / 270 : ℝ) ≤ (738906157711 / 5000000000000 : ℝ) :=
  log_rat_bounds (313 / 270 : ℝ) (1 / 1251 : ℝ) (-2) (-3) (3) (1477812315413 / 10000000000000 : ℝ) (738906157711 / 5000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hpsub_115 :
    IntervalIntegrable (fun t => Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1)) volume (22 / 15 : ℝ) (67 / 45 : ℝ) ∧
      (5273331991 / 10000000000000 : ℝ) ≤ ∫ t in (22 / 15 : ℝ)..(67 / 45 : ℝ), Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1) :=
  quad_prod_log_div_sub (11 / 5 : ℝ) (198 / 133 : ℝ) (313 / 270 : ℝ) (22 / 15 : ℝ) (67 / 45 : ℝ) (133 / 90 : ℝ) (1 / 90 : ℝ)
    (90 / 133 : ℝ) (90 / 313 : ℝ) (90 / 223 : ℝ) (1470119941992554403317753 / 25000000000000000000000000 : ℝ) (-30893143934912431828776093819 / 3315452500000000000000000000000 : ℝ) (-533785905345013488481690169913679641 / 3077823078331750000000000000000000000 : ℝ) (433416502658916907160935873102529127976701 / 2857225341491554982725000000000000000000000 : ℝ)
    (994794756181 / 2500000000000 : ℝ) (3979179024731 / 10000000000000 : ℝ) (1477812315413 / 10000000000000 : ℝ) (738906157711 / 5000000000000 : ℝ) (5273331991 / 10000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hlog_113 hlog_114 (by norm_num [quadProdLo])

private lemma hlog_116 : (3829922522557 / 10000000000000 : ℝ) ≤ Real.log (22 / 15 : ℝ) ∧ Real.log (22 / 15 : ℝ) ≤ (957480630641 / 2500000000000 : ℝ) :=
  log_rat_bounds (22 / 15 : ℝ) (1 / 109 : ℝ) (2) (2) (-2) (3829922522557 / 10000000000000 : ℝ) (957480630641 / 2500000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hlog_117 : (385376699567 / 2500000000000 : ℝ) ≤ Real.log (7 / 6 : ℝ) ∧ Real.log (7 / 6 : ℝ) ≤ (1541506798277 / 10000000000000 : ℝ) :=
  log_rat_bounds (7 / 6 : ℝ) (1 / 251 : ℝ) (-2) (-3) (3) (385376699567 / 2500000000000 : ℝ) (1541506798277 / 10000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hpsub_118 :
    IntervalIntegrable (fun t => Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1)) volume (67 / 45 : ℝ) (68 / 45 : ℝ) ∧
      (32795397 / 62500000000 : ℝ) ≤ ∫ t in (67 / 45 : ℝ)..(68 / 45 : ℝ), Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1) :=
  quad_prod_log_div_sub (11 / 5 : ℝ) (22 / 15 : ℝ) (7 / 6 : ℝ) (67 / 45 : ℝ) (68 / 45 : ℝ) (3 / 2 : ℝ) (1 / 90 : ℝ)
    (2 / 3 : ℝ) (2 / 7 : ℝ) (2 / 5 : ℝ) (1475962901340335769632819 / 25000000000000000000000000 : ℝ) (-22254971180709551162289199 / 1312500000000000000000000000 : ℝ) (-11374379029826380675591926821 / 68906250000000000000000000000 : ℝ) (1568045590223785420062291389723 / 10852734375000000000000000000000 : ℝ)
    (3829922522557 / 10000000000000 : ℝ) (957480630641 / 2500000000000 : ℝ) (385376699567 / 2500000000000 : ℝ) (1541506798277 / 10000000000000 : ℝ) (32795397 / 62500000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hlog_116 hlog_117 (by norm_num [quadProdLo])

private lemma hlog_119 : (184143052433 / 500000000000 : ℝ) ≤ Real.log (198 / 137 : ℝ) ∧ Real.log (198 / 137 : ℝ) ≤ (3682861048667 / 10000000000000 : ℝ) :=
  log_rat_bounds (198 / 137 : ℝ) (1 / 549 : ℝ) (2) (2) (-2) (184143052433 / 500000000000 : ℝ) (3682861048667 / 10000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hlog_120 : (320959629757 / 2000000000000 : ℝ) ≤ Real.log (317 / 270 : ℝ) ∧ Real.log (317 / 270 : ℝ) ≤ (1604798148793 / 10000000000000 : ℝ) :=
  log_rat_bounds (317 / 270 : ℝ) (19 / 20269 : ℝ) (-6) (1) (2) (320959629757 / 2000000000000 : ℝ) (1604798148793 / 10000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hpsub_121 :
    IntervalIntegrable (fun t => Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1)) volume (68 / 45 : ℝ) (23 / 15 : ℝ) ∧
      (5206697203 / 10000000000000 : ℝ) ≤ ∫ t in (68 / 45 : ℝ)..(23 / 15 : ℝ), Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1) :=
  quad_prod_log_div_sub (11 / 5 : ℝ) (198 / 137 : ℝ) (317 / 270 : ℝ) (68 / 45 : ℝ) (23 / 15 : ℝ) (137 / 90 : ℝ) (1 / 90 : ℝ)
    (90 / 137 : ℝ) (90 / 317 : ℝ) (90 / 227 : ℝ) (59102485931219518048781 / 1000000000000000000000000 : ℝ) (-23952593566090619544064590441 / 985838300000000000000000000000 : ℝ) (-152674834584372909047141120115640299 / 971877153746890000000000000000000000 : ℝ) (131899957274271262823052107247019282907439 / 958113721058672667887000000000000000000000 : ℝ)
    (184143052433 / 500000000000 : ℝ) (3682861048667 / 10000000000000 : ℝ) (320959629757 / 2000000000000 : ℝ) (1604798148793 / 10000000000000 : ℝ) (5206697203 / 10000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hlog_119 hlog_120 (by norm_num [quadProdLo])

private lemma hlog_122 : (1768965487817 / 5000000000000 : ℝ) ≤ Real.log (198 / 139 : ℝ) ∧ Real.log (198 / 139 : ℝ) ≤ (1768965487821 / 5000000000000 : ℝ) :=
  log_rat_bounds (198 / 139 : ℝ) (7 / 8903 : ℝ) (6) (-2) (-1) (1768965487817 / 5000000000000 : ℝ) (1768965487821 / 5000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hlog_123 : (83384571893 / 500000000000 : ℝ) ≤ Real.log (319 / 270 : ℝ) ∧ Real.log (319 / 270 : ℝ) ≤ (1667691437869 / 10000000000000 : ℝ) :=
  log_rat_bounds (319 / 270 : ℝ) (83 / 20333 : ℝ) (-6) (1) (2) (83384571893 / 500000000000 : ℝ) (1667691437869 / 10000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hpsub_124 :
    IntervalIntegrable (fun t => Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1)) volume (23 / 15 : ℝ) (14 / 9 : ℝ) ∧
      (5152455297 / 10000000000000 : ℝ) ≤ ∫ t in (23 / 15 : ℝ)..(14 / 9 : ℝ), Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1) :=
  quad_prod_log_div_sub (11 / 5 : ℝ) (198 / 139 : ℝ) (319 / 270 : ℝ) (23 / 15 : ℝ) (14 / 9 : ℝ) (139 / 90 : ℝ) (1 / 90 : ℝ)
    (90 / 139 : ℝ) (90 / 319 : ℝ) (90 / 229 : ℝ) (147504429895112452127581 / 2500000000000000000000000 : ℝ) (-7235309054786263150736511099 / 230774750000000000000000000000 : ℝ) (-3184265574871295463586180113839379 / 21302794095025000000000000000000000 : ℝ) (31221179546287527687051345790847438519661 / 237941513908514137947500000000000000000000 : ℝ)
    (1768965487817 / 5000000000000 : ℝ) (1768965487821 / 5000000000000 : ℝ) (83384571893 / 500000000000 : ℝ) (1667691437869 / 10000000000000 : ℝ) (5152455297 / 10000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hlog_122 hlog_123 (by norm_num [quadProdLo])

private lemma hlog_125 : (84876785079 / 250000000000 : ℝ) ≤ Real.log (66 / 47 : ℝ) ∧ Real.log (66 / 47 : ℝ) ≤ (3395071403167 / 10000000000000 : ℝ) :=
  log_rat_bounds (66 / 47 : ℝ) (13 / 2363 : ℝ) (-1) (-2) (2) (84876785079 / 250000000000 : ℝ) (3395071403167 / 10000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hlog_126 : (1730191641313 / 10000000000000 : ℝ) ≤ Real.log (107 / 90 : ℝ) ∧ Real.log (107 / 90 : ℝ) ≤ (43254791033 / 250000000000 : ℝ) :=
  log_rat_bounds (107 / 90 : ℝ) (1 / 641 : ℝ) (5) (-3) (0) (1730191641313 / 10000000000000 : ℝ) (43254791033 / 250000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hpsub_127 :
    IntervalIntegrable (fun t => Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1)) volume (14 / 9 : ℝ) (71 / 45 : ℝ) ∧
      (508531451 / 1000000000000 : ℝ) ≤ ∫ t in (14 / 9 : ℝ)..(71 / 45 : ℝ), Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1) :=
  quad_prod_log_div_sub (11 / 5 : ℝ) (66 / 47 : ℝ) (107 / 90 : ℝ) (14 / 9 : ℝ) (71 / 45 : ℝ) (47 / 30 : ℝ) (1 / 90 : ℝ)
    (30 / 47 : ℝ) (30 / 107 : ℝ) (30 / 77 : ℝ) (146853104085205758368727 / 2500000000000000000000000 : ℝ) (-3691786924889824526508984249 / 96808250000000000000000000000 : ℝ) (-533078937857779053866433954635337 / 3748734907225000000000000000000000 : ℝ) (18160389639096390020534673323583329319 / 145163386432945842500000000000000000000 : ℝ)
    (84876785079 / 250000000000 : ℝ) (3395071403167 / 10000000000000 : ℝ) (1730191641313 / 10000000000000 : ℝ) (43254791033 / 250000000000 : ℝ) (508531451 / 1000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hlog_125 hlog_126 (by norm_num [quadProdLo])

private lemma hlog_128 : (3254224004343 / 10000000000000 : ℝ) ≤ Real.log (18 / 13 : ℝ) ∧ Real.log (18 / 13 : ℝ) ≤ (3254224004349 / 10000000000000 : ℝ) :=
  log_rat_bounds (18 / 13 : ℝ) (1 / 79 : ℝ) (-2) (3) (-1) (3254224004343 / 10000000000000 : ℝ) (3254224004349 / 10000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hlog_129 : (1792303642239 / 10000000000000 : ℝ) ≤ Real.log (323 / 270 : ℝ) ∧ Real.log (323 / 270 : ℝ) ≤ (896151821123 / 5000000000000 : ℝ) :=
  log_rat_bounds (323 / 270 : ℝ) (3 / 643 : ℝ) (5) (-3) (0) (1792303642239 / 10000000000000 : ℝ) (896151821123 / 5000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hpsub_130 :
    IntervalIntegrable (fun t => Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1)) volume (71 / 45 : ℝ) (8 / 5 : ℝ) ∧
      (1001201763 / 2000000000000 : ℝ) ≤ ∫ t in (71 / 45 : ℝ)..(8 / 5 : ℝ), Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1) :=
  quad_prod_log_div_sub (11 / 5 : ℝ) (18 / 13 : ℝ) (323 / 270 : ℝ) (71 / 45 : ℝ) (8 / 5 : ℝ) (143 / 90 : ℝ) (1 / 90 : ℝ)
    (90 / 143 : ℝ) (90 / 323 : ℝ) (90 / 233 : ℝ) (5832557535645542254243977 / 100000000000000000000000000 : ℝ) (-22994995785051823543691270253 / 514930000000000000000000000000 : ℝ) (-74952886140497423291943995264557647 / 554169571241000000000000000000000000 : ℝ) (71158367589403876446767110895471878415547 / 596399342996977791700000000000000000000000 : ℝ)
    (3254224004343 / 10000000000000 : ℝ) (3254224004349 / 10000000000000 : ℝ) (1792303642239 / 10000000000000 : ℝ) (896151821123 / 5000000000000 : ℝ) (1001201763 / 2000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hlog_128 hlog_129 (by norm_num [quadProdLo])

private lemma hlog_131 : (194708305171 / 625000000000 : ℝ) ≤ Real.log (198 / 145 : ℝ) ∧ Real.log (198 / 145 : ℝ) ≤ (3115332882743 / 10000000000000 : ℝ) :=
  log_rat_bounds (198 / 145 : ℝ) (1 / 175 : ℝ) (-2) (3) (-1) (194708305171 / 625000000000 : ℝ) (3115332882743 / 10000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hlog_132 : (57938507291 / 312500000000 : ℝ) ≤ Real.log (65 / 54 : ℝ) ∧ Real.log (65 / 54 : ℝ) ≤ (463508058329 / 2500000000000 : ℝ) :=
  log_rat_bounds (65 / 54 : ℝ) (1 / 649 : ℝ) (1) (1) (-1) (57938507291 / 312500000000 : ℝ) (463508058329 / 2500000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hpsub_133 :
    IntervalIntegrable (fun t => Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1)) volume (8 / 5 : ℝ) (73 / 45 : ℝ) ∧
      (2457616037 / 5000000000000 : ℝ) ≤ ∫ t in (8 / 5 : ℝ)..(73 / 45 : ℝ), Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1) :=
  quad_prod_log_div_sub (11 / 5 : ℝ) (198 / 145 : ℝ) (65 / 54 : ℝ) (8 / 5 : ℝ) (73 / 45 : ℝ) (29 / 18 : ℝ) (1 / 90 : ℝ)
    (18 / 29 : ℝ) (18 / 65 : ℝ) (18 / 47 : ℝ) (11281108558768236501761 / 195312500000000000000000 : ℝ) (-88123784864865188950475073 / 1730371093750000000000000000 : ℝ) (-1971626589072101719322288077311 / 15330222705078125000000000000000 : ℝ) (15459429077718828084984375946316223 / 135818108055639648437500000000000000 : ℝ)
    (194708305171 / 625000000000 : ℝ) (3115332882743 / 10000000000000 : ℝ) (57938507291 / 312500000000 : ℝ) (463508058329 / 2500000000000 : ℝ) (2457616037 / 5000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hlog_131 hlog_132 (by norm_num [quadProdLo])

private lemma hlog_134 : (744586109789 / 2500000000000 : ℝ) ≤ Real.log (66 / 49 : ℝ) ∧ Real.log (66 / 49 : ℝ) ≤ (2978344439159 / 10000000000000 : ℝ) :=
  log_rat_bounds (66 / 49 : ℝ) (1 / 197 : ℝ) (2) (-1) (0) (744586109789 / 2500000000000 : ℝ) (2978344439159 / 10000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hlog_135 : (1915382118987 / 10000000000000 : ℝ) ≤ Real.log (109 / 90 : ℝ) ∧ Real.log (109 / 90 : ℝ) ≤ (1915382118991 / 10000000000000 : ℝ) :=
  log_rat_bounds (109 / 90 : ℝ) (1 / 217 : ℝ) (1) (1) (-1) (1915382118987 / 10000000000000 : ℝ) (1915382118991 / 10000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hpsub_136 :
    IntervalIntegrable (fun t => Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1)) volume (73 / 45 : ℝ) (74 / 45 : ℝ) ∧
      (1203410117 / 2500000000000 : ℝ) ≤ ∫ t in (73 / 45 : ℝ)..(74 / 45 : ℝ), Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1) :=
  quad_prod_log_div_sub (11 / 5 : ℝ) (66 / 49 : ℝ) (109 / 90 : ℝ) (73 / 45 : ℝ) (74 / 45 : ℝ) (49 / 30 : ℝ) (1 / 90 : ℝ)
    (30 / 49 : ℝ) (30 / 109 : ℝ) (30 / 79 : ℝ) (1426166920735941843463743 / 25000000000000000000000000 : ℝ) (-60082853340633353657819554089 / 1054847500000000000000000000000 : ℝ) (-5441565975360588907492007284831953 / 44508129930250000000000000000000000 : ℝ) (203982331109404016342351860224862382919 / 1877971583463975475000000000000000000000 : ℝ)
    (744586109789 / 2500000000000 : ℝ) (2978344439159 / 10000000000000 : ℝ) (1915382118987 / 10000000000000 : ℝ) (1915382118991 / 10000000000000 : ℝ) (1203410117 / 2500000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hlog_134 hlog_135 (by norm_num [quadProdLo])

private lemma hlog_137 : (1421603623743 / 5000000000000 : ℝ) ≤ Real.log (198 / 149 : ℝ) ∧ Real.log (198 / 149 : ℝ) ≤ (568641449499 / 2000000000000 : ℝ) :=
  log_rat_bounds (198 / 149 : ℝ) (383 / 37633 : ℝ) (-5) (-1) (3) (1421603623743 / 5000000000000 : ℝ) (568641449499 / 2000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hlog_138 : (494089479417 / 2500000000000 : ℝ) ≤ Real.log (329 / 270 : ℝ) ∧ Real.log (329 / 270 : ℝ) ≤ (247044739709 / 1250000000000 : ℝ) :=
  log_rat_bounds (329 / 270 : ℝ) (5 / 653 : ℝ) (1) (1) (-1) (494089479417 / 2500000000000 : ℝ) (247044739709 / 1250000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hpsub_139 :
    IntervalIntegrable (fun t => Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1)) volume (74 / 45 : ℝ) (5 / 3 : ℝ) ∧
      (4701854771 / 10000000000000 : ℝ) ≤ ∫ t in (74 / 45 : ℝ)..(5 / 3 : ℝ), Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1) :=
  quad_prod_log_div_sub (11 / 5 : ℝ) (198 / 149 : ℝ) (329 / 270 : ℝ) (74 / 45 : ℝ) (5 / 3 : ℝ) (149 / 90 : ℝ) (1 / 90 : ℝ)
    (90 / 149 : ℝ) (90 / 329 : ℝ) (90 / 239 : ℝ) (702399394392499610997831 / 12500000000000000000000000 : ℝ) (-919118280419328833376522061059 / 14645023750000000000000000000000 : ℝ) (-1993546637558331703732131858403440849 / 17158137651045125000000000000000000000 : ℝ) (2084188802742252019259174456669655664729461 / 20102506672426005435737500000000000000000000 : ℝ)
    (1421603623743 / 5000000000000 : ℝ) (568641449499 / 2000000000000 : ℝ) (494089479417 / 2500000000000 : ℝ) (247044739709 / 1250000000000 : ℝ) (4701854771 / 10000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hlog_137 hlog_138 (by norm_num [quadProdLo])

private lemma hlog_140 : (2709871938791 / 10000000000000 : ℝ) ≤ Real.log (198 / 151 : ℝ) ∧ Real.log (198 / 151 : ℝ) ≤ (2709871938801 / 10000000000000 : ℝ) :=
  log_rat_bounds (198 / 151 : ℝ) (133 / 37883 : ℝ) (-5) (-1) (3) (2709871938791 / 10000000000000 : ℝ) (2709871938801 / 10000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hlog_141 : (407392832757 / 2000000000000 : ℝ) ≤ Real.log (331 / 270 : ℝ) ∧ Real.log (331 / 270 : ℝ) ≤ (2036964163789 / 10000000000000 : ℝ) :=
  log_rat_bounds (331 / 270 : ℝ) (7 / 655 : ℝ) (1) (1) (-1) (407392832757 / 2000000000000 : ℝ) (2036964163789 / 10000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hpsub_142 :
    IntervalIntegrable (fun t => Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1)) volume (5 / 3 : ℝ) (76 / 45 : ℝ) ∧
      (229023123 / 500000000000 : ℝ) ≤ ∫ t in (5 / 3 : ℝ)..(76 / 45 : ℝ), Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1) :=
  quad_prod_log_div_sub (11 / 5 : ℝ) (198 / 151 : ℝ) (331 / 270 : ℝ) (5 / 3 : ℝ) (76 / 45 : ℝ) (151 / 90 : ℝ) (1 / 90 : ℝ)
    (90 / 151 : ℝ) (90 / 331 : ℝ) (90 / 241 : ℝ) (1103982405552769203776787 / 20000000000000000000000000 : ℝ) (-1646366236032895790165708319423 / 24090842000000000000000000000000 : ℝ) (-3202948925463301654670115592382271333 / 29018433413448200000000000000000000000 : ℝ) (3460003423014877634812451538841724731452057 / 34953924722545063069220000000000000000000000 : ℝ)
    (2709871938791 / 10000000000000 : ℝ) (2709871938801 / 10000000000000 : ℝ) (407392832757 / 2000000000000 : ℝ) (2036964163789 / 10000000000000 : ℝ) (229023123 / 500000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hlog_140 hlog_141 (by norm_num [quadProdLo])

private lemma hlog_143 : (2578291093017 / 10000000000000 : ℝ) ≤ Real.log (22 / 17 : ℝ) ∧ Real.log (22 / 17 : ℝ) ≤ (80571596657 / 312500000000 : ℝ) :=
  log_rat_bounds (22 / 17 : ℝ) (3 / 547 : ℝ) (5) (0) (-2) (2578291093017 / 10000000000000 : ℝ) (80571596657 / 312500000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hlog_144 : (1048602654909 / 5000000000000 : ℝ) ≤ Real.log (37 / 30 : ℝ) ∧ Real.log (37 / 30 : ℝ) ≤ (2097205309823 / 10000000000000 : ℝ) :=
  log_rat_bounds (37 / 30 : ℝ) (1 / 73 : ℝ) (1) (1) (-1) (1048602654909 / 5000000000000 : ℝ) (2097205309823 / 10000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hpsub_145 :
    IntervalIntegrable (fun t => Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1)) volume (76 / 45 : ℝ) (77 / 45 : ℝ) ∧
      (890003937 / 2000000000000 : ℝ) ≤ ∫ t in (76 / 45 : ℝ)..(77 / 45 : ℝ), Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1) :=
  quad_prod_log_div_sub (11 / 5 : ℝ) (22 / 17 : ℝ) (37 / 30 : ℝ) (76 / 45 : ℝ) (77 / 45 : ℝ) (17 / 10 : ℝ) (1 / 90 : ℝ)
    (10 / 17 : ℝ) (10 / 37 : ℝ) (10 / 27 : ℝ) (2703602885265853670670453 / 50000000000000000000000000 : ℝ) (-231812173292559887364878331 / 3145000000000000000000000000 : ℝ) (-62204295203222458149721281089 / 593461500000000000000000000000 : ℝ) (95276701166367410721174685804981 / 1007875665450000000000000000000000 : ℝ)
    (2578291093017 / 10000000000000 : ℝ) (80571596657 / 312500000000 : ℝ) (1048602654909 / 5000000000000 : ℝ) (2097205309823 / 10000000000000 : ℝ) (890003937 / 2000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hlog_143 hlog_144 (by norm_num [quadProdLo])

private lemma hlog_146 : (2448419137749 / 10000000000000 : ℝ) ≤ Real.log (198 / 155 : ℝ) ∧ Real.log (198 / 155 : ℝ) ≤ (2448419137757 / 10000000000000 : ℝ) :=
  log_rat_bounds (198 / 155 : ℝ) (13 / 2803 : ℝ) (-6) (4) (0) (2448419137749 / 10000000000000 : ℝ) (2448419137757 / 10000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hlog_147 : (1078542864131 / 5000000000000 : ℝ) ≤ Real.log (67 / 54 : ℝ) ∧ Real.log (67 / 54 : ℝ) ≤ (2157085728271 / 10000000000000 : ℝ) :=
  log_rat_bounds (67 / 54 : ℝ) (1 / 401 : ℝ) (2) (-4) (2) (1078542864131 / 5000000000000 : ℝ) (2157085728271 / 10000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hpsub_148 :
    IntervalIntegrable (fun t => Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1)) volume (77 / 45 : ℝ) (26 / 15 : ℝ) ∧
      (2155526553 / 5000000000000 : ℝ) ≤ ∫ t in (77 / 45 : ℝ)..(26 / 15 : ℝ), Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1) :=
  quad_prod_log_div_sub (11 / 5 : ℝ) (198 / 155 : ℝ) (67 / 54 : ℝ) (77 / 45 : ℝ) (26 / 15 : ℝ) (31 / 18 : ℝ) (1 / 90 : ℝ)
    (18 / 31 : ℝ) (18 / 67 : ℝ) (18 / 49 : ℝ) (2640724989420959880181119 / 50000000000000000000000000 : ℝ) (-200678442131199678040225657467 / 2544325000000000000000000000000 : ℝ) (-12881595017468733280271561784969369 / 129471794112500000000000000000000000 : ℝ) (594918148558826532771451159446432414717 / 6588366451105731250000000000000000000000 : ℝ)
    (2448419137749 / 10000000000000 : ℝ) (2448419137757 / 10000000000000 : ℝ) (1078542864131 / 5000000000000 : ℝ) (2157085728271 / 10000000000000 : ℝ) (2155526553 / 5000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hlog_146 hlog_147 (by norm_num [quadProdLo])

private lemma hlog_149 : (116010612673 / 500000000000 : ℝ) ≤ Real.log (198 / 157 : ℝ) ∧ Real.log (198 / 157 : ℝ) ≤ (290026531683 / 1250000000000 : ℝ) :=
  log_rat_bounds (198 / 157 : ℝ) (7 / 1577 : ℝ) (-2) (0) (1) (116010612673 / 500000000000 : ℝ) (290026531683 / 1250000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hlog_150 : (443321942707 / 2000000000000 : ℝ) ≤ Real.log (337 / 270 : ℝ) ∧ Real.log (337 / 270 : ℝ) ≤ (277076214193 / 1250000000000 : ℝ) :=
  log_rat_bounds (337 / 270 : ℝ) (11 / 2011 : ℝ) (2) (-4) (2) (443321942707 / 2000000000000 : ℝ) (277076214193 / 1250000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hpsub_151 :
    IntervalIntegrable (fun t => Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1)) volume (26 / 15 : ℝ) (79 / 45 : ℝ) ∧
      (4164061613 / 10000000000000 : ℝ) ≤ ∫ t in (26 / 15 : ℝ)..(79 / 45 : ℝ), Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1) :=
  quad_prod_log_div_sub (11 / 5 : ℝ) (198 / 157 : ℝ) (337 / 270 : ℝ) (26 / 15 : ℝ) (79 / 45 : ℝ) (157 / 90 : ℝ) (1 / 90 : ℝ)
    (90 / 157 : ℝ) (90 / 337 : ℝ) (90 / 247 : ℝ) (51430050184823674125811 / 1000000000000000000000000 : ℝ) (-109569591198272594468902807791 / 1306852300000000000000000000000 : ℝ) (-161216996075933377958559642083273829 / 1707862934015290000000000000000000000 : ℝ) (192554856202218408359270795209355415167049 / 2231924603402629971667000000000000000000000 : ℝ)
    (116010612673 / 500000000000 : ℝ) (290026531683 / 1250000000000 : ℝ) (443321942707 / 2000000000000 : ℝ) (277076214193 / 1250000000000 : ℝ) (4164061613 / 10000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hlog_149 hlog_150 (by norm_num [quadProdLo])

private lemma hlog_152 : (1096814142369 / 5000000000000 : ℝ) ≤ Real.log (66 / 53 : ℝ) ∧ Real.log (66 / 53 : ℝ) ≤ (2193628284747 / 10000000000000 : ℝ) :=
  log_rat_bounds (66 / 53 : ℝ) (23 / 5323 : ℝ) (2) (-4) (2) (1096814142369 / 5000000000000 : ℝ) (2193628284747 / 10000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hlog_153 : (2275781483819 / 10000000000000 : ℝ) ≤ Real.log (113 / 90 : ℝ) ∧ Real.log (113 / 90 : ℝ) ≤ (1137890741911 / 5000000000000 : ℝ) :=
  log_rat_bounds (113 / 90 : ℝ) (1 / 451 : ℝ) (-2) (0) (1) (2275781483819 / 10000000000000 : ℝ) (1137890741911 / 5000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hpsub_154 :
    IntervalIntegrable (fun t => Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1)) volume (79 / 45 : ℝ) (16 / 9 : ℝ) ∧
      (160380717 / 400000000000 : ℝ) ≤ ∫ t in (79 / 45 : ℝ)..(16 / 9 : ℝ), Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1) :=
  quad_prod_log_div_sub (11 / 5 : ℝ) (66 / 53 : ℝ) (113 / 90 : ℝ) (79 / 45 : ℝ) (16 / 9 : ℝ) (53 / 30 : ℝ) (1 / 90 : ℝ)
    (30 / 53 : ℝ) (30 / 113 : ℝ) (30 / 83 : ℝ) (2496109316394186735827211 / 50000000000000000000000000 : ℝ) (-220269351770293438082607500037 / 2485435000000000000000000000000 : ℝ) (-11059442216029705963547291046835221 / 123547742784500000000000000000000000 : ℝ) (506324267820143387114211123238488415707 / 6141397681751875150000000000000000000000 : ℝ)
    (1096814142369 / 5000000000000 : ℝ) (2193628284747 / 10000000000000 : ℝ) (2275781483819 / 10000000000000 : ℝ) (1137890741911 / 5000000000000 : ℝ) (160380717 / 400000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hlog_152 hlog_153 (by norm_num [quadProdLo])

private lemma hlog_155 : (2068626657099 / 10000000000000 : ℝ) ≤ Real.log (198 / 161 : ℝ) ∧ Real.log (198 / 161 : ℝ) ≤ (2068626657103 / 10000000000000 : ℝ) :=
  log_rat_bounds (198 / 161 : ℝ) (2 / 163 : ℝ) (1) (1) (-1) (2068626657099 / 10000000000000 : ℝ) (2068626657103 / 10000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hlog_156 : (46692103657 / 200000000000 : ℝ) ≤ Real.log (341 / 270 : ℝ) ∧ Real.log (341 / 270 : ℝ) ≤ (2334605182853 / 10000000000000 : ℝ) :=
  log_rat_bounds (341 / 270 : ℝ) (7 / 1357 : ℝ) (-2) (0) (1) (46692103657 / 200000000000 : ℝ) (2334605182853 / 10000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hpsub_157 :
    IntervalIntegrable (fun t => Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1)) volume (16 / 9 : ℝ) (9 / 5 : ℝ) ∧
      (961967523 / 2500000000000 : ℝ) ≤ ∫ t in (16 / 9 : ℝ)..(9 / 5 : ℝ), Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1) :=
  quad_prod_log_div_sub (11 / 5 : ℝ) (198 / 161 : ℝ) (341 / 270 : ℝ) (16 / 9 : ℝ) (9 / 5 : ℝ) (161 / 90 : ℝ) (1 / 90 : ℝ)
    (90 / 161 : ℝ) (90 / 341 : ℝ) (90 / 251 : ℝ) (96588530300899902911043 / 2000000000000000000000000 : ℝ) (-256931918775963339927472545687 / 2756030200000000000000000000000 : ℝ) (-322205836740614147187341367923142117 / 3797851231656020000000000000000000000 : ℝ) (412407441798253235787639789206535828288753 / 5233496344775593565902000000000000000000000 : ℝ)
    (2068626657099 / 10000000000000 : ℝ) (2068626657103 / 10000000000000 : ℝ) (46692103657 / 200000000000 : ℝ) (2334605182853 / 10000000000000 : ℝ) (961967523 / 2500000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hlog_155 hlog_156 (by norm_num [quadProdLo])

private lemma hlog_158 : (486292074719 / 2500000000000 : ℝ) ≤ Real.log (198 / 163 : ℝ) ∧ Real.log (198 / 163 : ℝ) ≤ (3039325467 / 15625000000 : ℝ) :=
  log_rat_bounds (198 / 163 : ℝ) (1 / 164 : ℝ) (1) (1) (-1) (486292074719 / 2500000000000 : ℝ) (3039325467 / 15625000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hlog_159 : (2393084881671 / 10000000000000 : ℝ) ≤ Real.log (343 / 270 : ℝ) ∧ Real.log (343 / 270 : ℝ) ≤ (29913561021 / 125000000000 : ℝ) :=
  log_rat_bounds (343 / 270 : ℝ) (41 / 21911 : ℝ) (-6) (4) (0) (2393084881671 / 10000000000000 : ℝ) (29913561021 / 125000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hpsub_160 :
    IntervalIntegrable (fun t => Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1)) volume (9 / 5 : ℝ) (82 / 45 : ℝ) ∧
      (1839771447 / 5000000000000 : ℝ) ≤ ∫ t in (9 / 5 : ℝ)..(82 / 45 : ℝ), Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1) :=
  quad_prod_log_div_sub (11 / 5 : ℝ) (198 / 163 : ℝ) (343 / 270 : ℝ) (9 / 5 : ℝ) (82 / 45 : ℝ) (163 / 90 : ℝ) (1 / 90 : ℝ)
    (90 / 163 : ℝ) (90 / 343 : ℝ) (90 / 253 : ℝ) (1163738212086463205575449 / 25000000000000000000000000 : ℝ) (-313932463668403309522241818479 / 3214767500000000000000000000000 : ℝ) (-33218935055279340378087053594174391 / 413389203162250000000000000000000000 : ℝ) (44050510268681812465767852527070264237771 / 584738077077835351825000000000000000000000 : ℝ)
    (486292074719 / 2500000000000 : ℝ) (3039325467 / 15625000000 : ℝ) (2393084881671 / 10000000000000 : ℝ) (29913561021 / 125000000000 : ℝ) (1839771447 / 5000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hlog_158 hlog_159 (by norm_num [quadProdLo])

private lemma hlog_161 : (1823215567937 / 10000000000000 : ℝ) ≤ Real.log (6 / 5 : ℝ) ∧ Real.log (6 / 5 : ℝ) ≤ (1823215567941 / 10000000000000 : ℝ) :=
  log_rat_bounds (6 / 5 : ℝ) (0 : ℝ) (1) (1) (-1) (1823215567937 / 10000000000000 : ℝ) (1823215567941 / 10000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hlog_162 : (98048983213 / 400000000000 : ℝ) ≤ Real.log (23 / 18 : ℝ) ∧ Real.log (23 / 18 : ℝ) ≤ (1225612290167 / 5000000000000 : ℝ) :=
  log_rat_bounds (23 / 18 : ℝ) (7 / 1465 : ℝ) (-6) (4) (0) (98048983213 / 400000000000 : ℝ) (1225612290167 / 5000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hpsub_163 :
    IntervalIntegrable (fun t => Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1)) volume (82 / 45 : ℝ) (83 / 45 : ℝ) ∧
      (876234789 / 2500000000000 : ℝ) ≤ ∫ t in (82 / 45 : ℝ)..(83 / 45 : ℝ), Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1) :=
  quad_prod_log_div_sub (11 / 5 : ℝ) (6 / 5 : ℝ) (23 / 18 : ℝ) (82 / 45 : ℝ) (83 / 45 : ℝ) (11 / 6 : ℝ) (1 / 90 : ℝ)
    (6 / 11 : ℝ) (6 / 23 : ℝ) (6 / 17 : ℝ) (178764432614335174041581 / 4000000000000000000000000 : ℝ) (-876667203997707597097559979 / 8602000000000000000000000000 : ℝ) (-1407040240400680664202951975939 / 18498601000000000000000000000000 : ℝ) (2865499904480493508219640549737701 / 39781241450500000000000000000000000 : ℝ)
    (1823215567937 / 10000000000000 : ℝ) (1823215567941 / 10000000000000 : ℝ) (98048983213 / 400000000000 : ℝ) (1225612290167 / 5000000000000 : ℝ) (876234789 / 2500000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hlog_161 hlog_162 (by norm_num [quadProdLo])

private lemma hlog_164 : (851366091387 / 5000000000000 : ℝ) ≤ Real.log (198 / 167 : ℝ) ∧ Real.log (198 / 167 : ℝ) ≤ (1702732182781 / 10000000000000 : ℝ) :=
  log_rat_bounds (198 / 167 : ℝ) (1 / 5345 : ℝ) (5) (-3) (0) (851366091387 / 5000000000000 : ℝ) (1702732182781 / 10000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hlog_165 : (2509028209481 / 10000000000000 : ℝ) ≤ Real.log (347 / 270 : ℝ) ∧ Real.log (347 / 270 : ℝ) ≤ (156814263093 / 625000000000 : ℝ) :=
  log_rat_bounds (347 / 270 : ℝ) (7 / 3463 : ℝ) (5) (0) (-2) (2509028209481 / 10000000000000 : ℝ) (156814263093 / 625000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hpsub_166 :
    IntervalIntegrable (fun t => Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1)) volume (83 / 45 : ℝ) (28 / 15 : ℝ) ∧
      (207777561 / 625000000000 : ℝ) ≤ ∫ t in (83 / 45 : ℝ)..(28 / 15 : ℝ), Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1) :=
  quad_prod_log_div_sub (11 / 5 : ℝ) (198 / 167 : ℝ) (347 / 270 : ℝ) (83 / 45 : ℝ) (28 / 15 : ℝ) (167 / 90 : ℝ) (1 / 90 : ℝ)
    (90 / 167 : ℝ) (90 / 347 : ℝ) (90 / 257 : ℝ) (2136101539885562025840147 / 50000000000000000000000000 : ℝ) (-7894352419550751589518696106527 / 74464465000000000000000000000000 : ℝ) (-7978488639289835816183162213905801893 / 110899130954724500000000000000000000000 : ℝ) (11377186526927148870827895021707645825077113 / 165160889110169982297850000000000000000000000 : ℝ)
    (851366091387 / 5000000000000 : ℝ) (1702732182781 / 10000000000000 : ℝ) (2509028209481 / 10000000000000 : ℝ) (156814263093 / 625000000000 : ℝ) (207777561 / 625000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hlog_164 hlog_165 (by norm_num [quadProdLo])

private lemma hlog_167 : (158368315771 / 1000000000000 : ℝ) ≤ Real.log (198 / 169 : ℝ) ∧ Real.log (198 / 169 : ℝ) ≤ (1583683157719 / 10000000000000 : ℝ) :=
  log_rat_bounds (198 / 169 : ℝ) (259 / 42509 : ℝ) (-2) (-3) (3) (158368315771 / 1000000000000 : ℝ) (1583683157719 / 10000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hlog_168 : (2566499632037 / 10000000000000 : ℝ) ≤ Real.log (349 / 270 : ℝ) ∧ Real.log (349 / 270 : ℝ) ≤ (641624908011 / 2500000000000 : ℝ) :=
  log_rat_bounds (349 / 270 : ℝ) (17 / 3473 : ℝ) (5) (0) (-2) (2566499632037 / 10000000000000 : ℝ) (641624908011 / 2500000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hpsub_169 :
    IntervalIntegrable (fun t => Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1)) volume (28 / 15 : ℝ) (17 / 9 : ℝ) ∧
      (784602719 / 2500000000000 : ℝ) ≤ ∫ t in (28 / 15 : ℝ)..(17 / 9 : ℝ), Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1) :=
  quad_prod_log_div_sub (11 / 5 : ℝ) (198 / 169 : ℝ) (349 / 270 : ℝ) (28 / 15 : ℝ) (17 / 9 : ℝ) (169 / 90 : ℝ) (1 / 90 : ℝ)
    (90 / 169 : ℝ) (90 / 349 : ℝ) (90 / 259 : ℝ) (406452224152590923955527 / 10000000000000000000000000 : ℝ) (-1679778282384684200572388441883 / 15276079000000000000000000000000 : ℝ) (-1586706227468960628175636115783688993 / 23335858961424100000000000000000000000 : ℝ) (2348754965817457498243385175774339844465197 / 35648042502757250410390000000000000000000000 : ℝ)
    (158368315771 / 1000000000000 : ℝ) (1583683157719 / 10000000000000 : ℝ) (2566499632037 / 10000000000000 : ℝ) (641624908011 / 2500000000000 : ℝ) (784602719 / 2500000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hlog_167 hlog_168 (by norm_num [quadProdLo])

private lemma hlog_170 : (733017370957 / 5000000000000 : ℝ) ≤ Real.log (22 / 19 : ℝ) ∧ Real.log (22 / 19 : ℝ) ≤ (1466034741923 / 10000000000000 : ℝ) :=
  log_rat_bounds (22 / 19 : ℝ) (1 / 4751 : ℝ) (-2) (-3) (3) (733017370957 / 5000000000000 : ℝ) (1466034741923 / 10000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hlog_171 : (262364264467 / 1000000000000 : ℝ) ≤ Real.log (13 / 10 : ℝ) ∧ Real.log (13 / 10 : ℝ) ≤ (65591066117 / 250000000000 : ℝ) :=
  log_rat_bounds (13 / 10 : ℝ) (1 / 649 : ℝ) (1) (4) (-3) (262364264467 / 1000000000000 : ℝ) (65591066117 / 250000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hpsub_172 :
    IntervalIntegrable (fun t => Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1)) volume (17 / 9 : ℝ) (86 / 45 : ℝ) ∧
      (589438577 / 2000000000000 : ℝ) ≤ ∫ t in (17 / 9 : ℝ)..(86 / 45 : ℝ), Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1) :=
  quad_prod_log_div_sub (11 / 5 : ℝ) (22 / 19 : ℝ) (13 / 10 : ℝ) (17 / 9 : ℝ) (86 / 45 : ℝ) (19 / 10 : ℝ) (1 / 90 : ℝ)
    (10 / 19 : ℝ) (10 / 39 : ℝ) (10 / 29 : ℝ) (192317563372667392884919 / 5000000000000000000000000 : ℝ) (-1222284658622724538127724979 / 10744500000000000000000000000 : ℝ) (-1482449134130838728247355790561 / 23088856050000000000000000000000 : ℝ) (9381682235882871077915871922417103 / 148846928297535000000000000000000000 : ℝ)
    (733017370957 / 5000000000000 : ℝ) (1466034741923 / 10000000000000 : ℝ) (262364264467 / 1000000000000 : ℝ) (65591066117 / 250000000000 : ℝ) (589438577 / 2000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hlog_170 hlog_171 (by norm_num [quadProdLo])

private lemma hlog_173 : (269950872393 / 2000000000000 : ℝ) ≤ Real.log (198 / 173 : ℝ) ∧ Real.log (198 / 173 : ℝ) ≤ (134975436197 / 1000000000000 : ℝ) :=
  log_rat_bounds (198 / 173 : ℝ) (3 / 349 : ℝ) (-3) (2) (0) (269950872393 / 2000000000000 : ℝ) (134975436197 / 1000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hlog_174 : (167528811209 / 625000000000 : ℝ) ≤ Real.log (353 / 270 : ℝ) ∧ Real.log (353 / 270 : ℝ) ≤ (1340230489677 / 5000000000000 : ℝ) :=
  log_rat_bounds (353 / 270 : ℝ) (23 / 11273 : ℝ) (-5) (-1) (3) (167528811209 / 625000000000 : ℝ) (1340230489677 / 5000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hpsub_175 :
    IntervalIntegrable (fun t => Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1)) volume (86 / 45 : ℝ) (29 / 15 : ℝ) ∧
      (2751113549 / 10000000000000 : ℝ) ≤ ∫ t in (86 / 45 : ℝ)..(29 / 15 : ℝ), Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1) :=
  quad_prod_log_div_sub (11 / 5 : ℝ) (198 / 173 : ℝ) (353 / 270 : ℝ) (86 / 45 : ℝ) (29 / 15 : ℝ) (173 / 90 : ℝ) (1 / 90 : ℝ)
    (90 / 173 : ℝ) (90 / 353 : ℝ) (90 / 263 : ℝ) (45224548736831747053137 / 1250000000000000000000000 : ℝ) (-235725060240842292772092211077 / 2007643375000000000000000000000 : ℝ) (-195315012189950033345336219355648183 / 3224505536945112500000000000000000000 : ℝ) (312305435684817841316025675013095709988643 / 5178925743118938279403750000000000000000000 : ℝ)
    (269950872393 / 2000000000000 : ℝ) (134975436197 / 1000000000000 : ℝ) (167528811209 / 625000000000 : ℝ) (1340230489677 / 5000000000000 : ℝ) (2751113549 / 10000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hlog_173 hlog_174 (by norm_num [quadProdLo])

private lemma hlog_176 : (308702641927 / 2500000000000 : ℝ) ≤ Real.log (198 / 175 : ℝ) ∧ Real.log (198 / 175 : ℝ) ≤ (1234810567713 / 10000000000000 : ℝ) :=
  log_rat_bounds (198 / 175 : ℝ) (1 / 351 : ℝ) (-3) (2) (0) (308702641927 / 2500000000000 : ℝ) (1234810567713 / 10000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hlog_177 : (1368479152383 / 5000000000000 : ℝ) ≤ Real.log (71 / 54 : ℝ) ∧ Real.log (71 / 54 : ℝ) ≤ (109478332191 / 400000000000 : ℝ) :=
  log_rat_bounds (71 / 54 : ℝ) (11 / 2261 : ℝ) (-5) (-1) (3) (1368479152383 / 5000000000000 : ℝ) (109478332191 / 400000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hpsub_178 :
    IntervalIntegrable (fun t => Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1)) volume (29 / 15 : ℝ) (88 / 45 : ℝ) ∧
      (637620721 / 2500000000000 : ℝ) ≤ ∫ t in (29 / 15 : ℝ)..(88 / 45 : ℝ), Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1) :=
  quad_prod_log_div_sub (11 / 5 : ℝ) (198 / 175 : ℝ) (71 / 54 : ℝ) (29 / 15 : ℝ) (88 / 45 : ℝ) (35 / 18 : ℝ) (1 / 90 : ℝ)
    (18 / 35 : ℝ) (18 / 71 : ℝ) (18 / 53 : ℝ) (422453129762653717762041 / 12500000000000000000000000 : ℝ) (-2844140567047802225649944199 / 23518750000000000000000000000 : ℝ) (-17682238791012665555117799597873 / 309753696875000000000000000000000 : ℝ) (235403873829785491999625937601285929 / 4079611064692187500000000000000000000 : ℝ)
    (308702641927 / 2500000000000 : ℝ) (1234810567713 / 10000000000000 : ℝ) (1368479152383 / 5000000000000 : ℝ) (109478332191 / 400000000000 : ℝ) (637620721 / 2500000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hlog_176 hlog_177 (by norm_num [quadProdLo])

private lemma hlog_179 : (224234596241 / 2000000000000 : ℝ) ≤ Real.log (66 / 59 : ℝ) ∧ Real.log (66 / 59 : ℝ) ≤ (1121172981209 / 10000000000000 : ℝ) :=
  log_rat_bounds (66 / 59 : ℝ) (1 / 296 : ℝ) (1) (-2) (1) (224234596241 / 2000000000000 : ℝ) (1121172981209 / 10000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hlog_180 : (87285569619 / 312500000000 : ℝ) ≤ Real.log (119 / 90 : ℝ) ∧ Real.log (119 / 90 : ℝ) ≤ (2793138227817 / 10000000000000 : ℝ) :=
  log_rat_bounds (119 / 90 : ℝ) (29 / 3779 : ℝ) (-5) (-1) (3) (87285569619 / 312500000000 : ℝ) (2793138227817 / 10000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hpsub_181 :
    IntervalIntegrable (fun t => Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1)) volume (88 / 45 : ℝ) (89 / 45 : ℝ) ∧
      (2345595269 / 10000000000000 : ℝ) ≤ ∫ t in (88 / 45 : ℝ)..(89 / 45 : ℝ), Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1) :=
  quad_prod_log_div_sub (11 / 5 : ℝ) (66 / 59 : ℝ) (119 / 90 : ℝ) (88 / 45 : ℝ) (89 / 45 : ℝ) (59 / 30 : ℝ) (1 / 90 : ℝ)
    (30 / 59 : ℝ) (30 / 119 : ℝ) (30 / 89 : ℝ) (19572444461182161202179 / 625000000000000000000000 : ℝ) (-4855038331387206048901496277 / 39054312500000000000000000000 : ℝ) (-131141126153050901536144033917549 / 2440382919756250000000000000000000 : ℝ) (8420706815782702955997850723905334587 / 152491963468516818125000000000000000000 : ℝ)
    (224234596241 / 2000000000000 : ℝ) (1121172981209 / 10000000000000 : ℝ) (87285569619 / 312500000000 : ℝ) (2793138227817 / 10000000000000 : ℝ) (2345595269 / 10000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hlog_179 hlog_180 (by norm_num [quadProdLo])

private lemma hlog_182 : (504406124267 / 5000000000000 : ℝ) ≤ Real.log (198 / 179 : ℝ) ∧ Real.log (198 / 179 : ℝ) ≤ (1008812248541 / 10000000000000 : ℝ) :=
  log_rat_bounds (198 / 179 : ℝ) (13 / 1087 : ℝ) (0) (3) (-2) (504406124267 / 5000000000000 : ℝ) (1008812248541 / 10000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hlog_183 : (1424502147447 / 5000000000000 : ℝ) ≤ Real.log (359 / 270 : ℝ) ∧ Real.log (359 / 270 : ℝ) ≤ (356125536863 / 1250000000000 : ℝ) :=
  log_rat_bounds (359 / 270 : ℝ) (119 / 11369 : ℝ) (-5) (-1) (3) (1424502147447 / 5000000000000 : ℝ) (356125536863 / 1250000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hpsub_184 :
    IntervalIntegrable (fun t => Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1)) volume (89 / 45 : ℝ) (2 : ℝ) ∧
      (534182571 / 2500000000000 : ℝ) ≤ ∫ t in (89 / 45 : ℝ)..(2 : ℝ), Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1) :=
  quad_prod_log_div_sub (11 / 5 : ℝ) (198 / 179 : ℝ) (359 / 270 : ℝ) (89 / 45 : ℝ) (2 : ℝ) (179 / 90 : ℝ) (1 / 90 : ℝ)
    (90 / 179 : ℝ) (90 / 359 : ℝ) (90 / 269 : ℝ) (718527607203759838796349 / 25000000000000000000000000 : ℝ) (-5513066914717263699008029647801 / 43215522500000000000000000000000 : ℝ) (-3774390595239796832881755061223939451 / 74703255397920250000000000000000000000 : ℝ) (6824882724785003944851315200903804157546399 / 129133608578882760683225000000000000000000000 : ℝ)
    (504406124267 / 5000000000000 : ℝ) (1008812248541 / 10000000000000 : ℝ) (1424502147447 / 5000000000000 : ℝ) (356125536863 / 1250000000000 : ℝ) (534182571 / 2500000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hlog_182 hlog_183 (by norm_num [quadProdLo])

private lemma hlog_185 : (224424998571 / 2500000000000 : ℝ) ≤ Real.log (198 / 181 : ℝ) ∧ Real.log (198 / 181 : ℝ) ≤ (89769999429 / 1000000000000 : ℝ) :=
  log_rat_bounds (198 / 181 : ℝ) (7 / 1093 : ℝ) (0) (3) (-2) (224424998571 / 2500000000000 : ℝ) (89769999429 / 1000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hlog_186 : (2904559993343 / 10000000000000 : ℝ) ≤ Real.log (361 / 270 : ℝ) ∧ Real.log (361 / 270 : ℝ) ≤ (2904559993347 / 10000000000000 : ℝ) :=
  log_rat_bounds (361 / 270 : ℝ) (1 / 721 : ℝ) (2) (-1) (0) (2904559993343 / 10000000000000 : ℝ) (2904559993347 / 10000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hpsub_187 :
    IntervalIntegrable (fun t => Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1)) volume (2 : ℝ) (91 / 45 : ℝ) ∧
      (384830701 / 2000000000000 : ℝ) ≤ ∫ t in (2 : ℝ)..(91 / 45 : ℝ), Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1) :=
  quad_prod_log_div_sub (11 / 5 : ℝ) (198 / 181 : ℝ) (361 / 270 : ℝ) (2 : ℝ) (91 / 45 : ℝ) (181 / 90 : ℝ) (1 / 90 : ℝ)
    (90 / 181 : ℝ) (90 / 361 : ℝ) (90 / 271 : ℝ) (651855872355386544512853 / 25000000000000000000000000 : ℝ) (-5786102072505237162345128950857 / 44268527500000000000000000000000 : ℝ) (-3718767985924178350187038612998474867 / 78388101080730250000000000000000000000 : ℝ) (7021967569133883156770071972989900116561823 / 138805032334603471688275000000000000000000000 : ℝ)
    (224424998571 / 2500000000000 : ℝ) (89769999429 / 1000000000000 : ℝ) (2904559993343 / 10000000000000 : ℝ) (2904559993347 / 10000000000000 : ℝ) (384830701 / 2000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hlog_185 hlog_186 (by norm_num [quadProdLo])

private lemma hlog_188 : (24619024329 / 312500000000 : ℝ) ≤ Real.log (66 / 61 : ℝ) ∧ Real.log (66 / 61 : ℝ) ≤ (393904389267 / 5000000000000 : ℝ) :=
  log_rat_bounds (66 / 61 : ℝ) (1 / 1099 : ℝ) (0) (3) (-2) (24619024329 / 312500000000 : ℝ) (393904389267 / 5000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hlog_189 : (2959808752663 / 10000000000000 : ℝ) ≤ Real.log (121 / 90 : ℝ) ∧ Real.log (121 / 90 : ℝ) ≤ (1479904376333 / 5000000000000 : ℝ) :=
  log_rat_bounds (121 / 90 : ℝ) (1 / 241 : ℝ) (2) (-1) (0) (2959808752663 / 10000000000000 : ℝ) (1479904376333 / 5000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hpsub_190 :
    IntervalIntegrable (fun t => Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1)) volume (91 / 45 : ℝ) (92 / 45 : ℝ) ∧
      (1708117237 / 10000000000000 : ℝ) ≤ ∫ t in (91 / 45 : ℝ)..(92 / 45 : ℝ), Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1) :=
  quad_prod_log_div_sub (11 / 5 : ℝ) (66 / 61 : ℝ) (121 / 90 : ℝ) (91 / 45 : ℝ) (92 / 45 : ℝ) (61 / 30 : ℝ) (1 / 90 : ℝ)
    (30 / 61 : ℝ) (30 / 121 : ℝ) (30 / 91 : ℝ) (72867603690997540538127 / 3125000000000000000000000 : ℝ) (-4009607430945773318233678023 / 29985312500000000000000000000 : ℝ) (-89580588325043048779195417536711 / 2014026483218750000000000000000000 : ℝ) (6551070753653112917130513193015391673 / 135276318201002103125000000000000000000 : ℝ)
    (24619024329 / 312500000000 : ℝ) (393904389267 / 5000000000000 : ℝ) (2959808752663 / 10000000000000 : ℝ) (1479904376333 / 5000000000000 : ℝ) (1708117237 / 10000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hlog_188 hlog_189 (by norm_num [quadProdLo])

private lemma hlog_191 : (679112056159 / 10000000000000 : ℝ) ≤ Real.log (198 / 185 : ℝ) ∧ Real.log (198 / 185 : ℝ) ≤ (135822411233 / 2000000000000 : ℝ) :=
  log_rat_bounds (198 / 185 : ℝ) (1 / 593 : ℝ) (4) (-1) (-1) (679112056159 / 10000000000000 : ℝ) (135822411233 / 2000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hlog_192 : (1507376972919 / 5000000000000 : ℝ) ≤ Real.log (73 / 54 : ℝ) ∧ Real.log (73 / 54 : ℝ) ≤ (753688486461 / 2500000000000 : ℝ) :=
  log_rat_bounds (73 / 54 : ℝ) (1 / 1459 : ℝ) (-2) (3) (-1) (1507376972919 / 5000000000000 : ℝ) (753688486461 / 2500000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hpsub_193 :
    IntervalIntegrable (fun t => Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1)) volume (92 / 45 : ℝ) (31 / 15 : ℝ) ∧
      (744430611 / 5000000000000 : ℝ) ≤ ∫ t in (92 / 45 : ℝ)..(31 / 15 : ℝ), Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1) :=
  quad_prod_log_div_sub (11 / 5 : ℝ) (198 / 185 : ℝ) (73 / 54 : ℝ) (92 / 45 : ℝ) (31 / 15 : ℝ) (37 / 18 : ℝ) (1 / 90 : ℝ)
    (18 / 37 : ℝ) (18 / 73 : ℝ) (18 / 55 : ℝ) (1023677875485751350158121 / 50000000000000000000000000 : ℝ) (-13713123462073063637053885497 / 100375000000000000000000000000 : ℝ) (-310402536879106110859357097453427 / 7455604062500000000000000000000000 : ℝ) (25674533212210554746085736681995356943 / 553783630752343750000000000000000000000 : ℝ)
    (679112056159 / 10000000000000 : ℝ) (135822411233 / 2000000000000 : ℝ) (1507376972919 / 5000000000000 : ℝ) (753688486461 / 2500000000000 : ℝ) (744430611 / 5000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hlog_191 hlog_192 (by norm_num [quadProdLo])

private lemma hlog_194 : (114316827679 / 2000000000000 : ℝ) ≤ Real.log (18 / 17 : ℝ) ∧ Real.log (18 / 17 : ℝ) ≤ (142896034601 / 2500000000000 : ℝ) :=
  log_rat_bounds (18 / 17 : ℝ) (1 / 511 : ℝ) (-7) (3) (1) (114316827679 / 2000000000000 : ℝ) (142896034601 / 2500000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hlog_195 : (3069398890559 / 10000000000000 : ℝ) ≤ Real.log (367 / 270 : ℝ) ∧ Real.log (367 / 270 : ℝ) ≤ (613879778113 / 2000000000000 : ℝ) :=
  log_rat_bounds (367 / 270 : ℝ) (5 / 1463 : ℝ) (-2) (3) (-1) (3069398890559 / 10000000000000 : ℝ) (613879778113 / 2000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hpsub_196 :
    IntervalIntegrable (fun t => Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1)) volume (31 / 15 : ℝ) (94 / 45 : ℝ) ∧
      (1266613289 / 10000000000000 : ℝ) ≤ ∫ t in (31 / 15 : ℝ)..(94 / 45 : ℝ), Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1) :=
  quad_prod_log_div_sub (11 / 5 : ℝ) (18 / 17 : ℝ) (367 / 270 : ℝ) (31 / 15 : ℝ) (94 / 45 : ℝ) (187 / 90 : ℝ) (1 / 90 : ℝ)
    (90 / 187 : ℝ) (90 / 367 : ℝ) (90 / 277 : ℝ) (350883944050146982982561 / 20000000000000000000000000 : ℝ) (-5300368958317023803655991609821 / 38020466000000000000000000000000 : ℝ) (-2811655532338102295916632566286351319 / 72277791742857800000000000000000000000 : ℝ) (6098984139247251006752718459908994042044859 / 137401766175720286386740000000000000000000000 : ℝ)
    (114316827679 / 2000000000000 : ℝ) (142896034601 / 2500000000000 : ℝ) (3069398890559 / 10000000000000 : ℝ) (613879778113 / 2000000000000 : ℝ) (1266613289 / 10000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hlog_194 hlog_195 (by norm_num [quadProdLo])

private lemma hlog_197 : (232600078173 / 5000000000000 : ℝ) ≤ Real.log (22 / 21 : ℝ) ∧ Real.log (22 / 21 : ℝ) ≤ (7268752443 / 156250000000 : ℝ) :=
  log_rat_bounds (22 / 21 : ℝ) (1 / 351 : ℝ) (-3) (-1) (2) (232600078173 / 5000000000000 : ℝ) (7268752443 / 156250000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hlog_198 : (1561873425209 / 5000000000000 : ℝ) ≤ Real.log (41 / 30 : ℝ) ∧ Real.log (41 / 30 : ℝ) ≤ (124949874017 / 400000000000 : ℝ) :=
  log_rat_bounds (41 / 30 : ℝ) (1 / 163 : ℝ) (-2) (3) (-1) (1561873425209 / 5000000000000 : ℝ) (124949874017 / 400000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hpsub_199 :
    IntervalIntegrable (fun t => Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1)) volume (94 / 45 : ℝ) (19 / 9 : ℝ) ∧
      (52079499 / 500000000000 : ℝ) ≤ ∫ t in (94 / 45 : ℝ)..(19 / 9 : ℝ), Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1) :=
  quad_prod_log_div_sub (11 / 5 : ℝ) (22 / 21 : ℝ) (41 / 30 : ℝ) (94 / 45 : ℝ) (19 / 9 : ℝ) (21 / 10 : ℝ) (1 / 90 : ℝ)
    (10 / 21 : ℝ) (10 / 41 : ℝ) (10 / 31 : ℝ) (363291880799944668863157 / 25000000000000000000000000 : ℝ) (-9481386672118832359891178177 / 66727500000000000000000000000 : ℝ) (-6460705519897543848133695589603 / 178102370250000000000000000000000 : ℝ) (60610844479285493815849335707944549 / 1426119109302825000000000000000000000 : ℝ)
    (232600078173 / 5000000000000 : ℝ) (7268752443 / 156250000000 : ℝ) (1561873425209 / 5000000000000 : ℝ) (124949874017 / 400000000000 : ℝ) (52079499 / 500000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hlog_197 hlog_198 (by norm_num [quadProdLo])

private lemma hlog_200 : (179968013237 / 5000000000000 : ℝ) ≤ Real.log (198 / 191 : ℝ) ∧ Real.log (198 / 191 : ℝ) ≤ (89984006621 / 2500000000000 : ℝ) :=
  log_rat_bounds (198 / 191 : ℝ) (151 / 24599 : ℝ) (7) (0) (-3) (179968013237 / 5000000000000 : ℝ) (89984006621 / 2500000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hlog_201 : (3177801036087 / 10000000000000 : ℝ) ≤ Real.log (371 / 270 : ℝ) ∧ Real.log (371 / 270 : ℝ) ≤ (1588900518047 / 5000000000000 : ℝ) :=
  log_rat_bounds (371 / 270 : ℝ) (13 / 1471 : ℝ) (-2) (3) (-1) (3177801036087 / 10000000000000 : ℝ) (1588900518047 / 5000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hpsub_202 :
    IntervalIntegrable (fun t => Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1)) volume (19 / 9 : ℝ) (32 / 15 : ℝ) ∧
      (813997129 / 10000000000000 : ℝ) ≤ ∫ t in (19 / 9 : ℝ)..(32 / 15 : ℝ), Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1) :=
  quad_prod_log_div_sub (11 / 5 : ℝ) (198 / 191 : ℝ) (371 / 270 : ℝ) (19 / 9 : ℝ) (32 / 15 : ℝ) (191 / 90 : ℝ) (1 / 90 : ℝ)
    (90 / 191 : ℝ) (90 / 371 : ℝ) (90 / 281 : ℝ) (571902538927057530683619 / 50000000000000000000000000 : ℝ) (-14403416692428082248135947333631 / 99559705000000000000000000000000 : ℝ) (-6691192977405176069540815223924163381 / 198242697193740500000000000000000000000 : ℝ) (16064123365895771394922523233297411272069369 / 394739689020262640531050000000000000000000000 : ℝ)
    (179968013237 / 5000000000000 : ℝ) (89984006621 / 2500000000000 : ℝ) (3177801036087 / 10000000000000 : ℝ) (1588900518047 / 5000000000000 : ℝ) (813997129 / 10000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hlog_200 hlog_201 (by norm_num [quadProdLo])

private lemma hlog_203 : (63942104473 / 2500000000000 : ℝ) ≤ Real.log (198 / 193 : ℝ) ∧ Real.log (198 / 193 : ℝ) ≤ (255768417901 / 10000000000000 : ℝ) :=
  log_rat_bounds (198 / 193 : ℝ) (23 / 24727 : ℝ) (7) (0) (-3) (63942104473 / 2500000000000 : ℝ) (255768417901 / 10000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hlog_204 : (3231564606451 / 10000000000000 : ℝ) ≤ Real.log (373 / 270 : ℝ) ∧ Real.log (373 / 270 : ℝ) ≤ (1615782303229 / 5000000000000 : ℝ) :=
  log_rat_bounds (373 / 270 : ℝ) (17 / 1475 : ℝ) (-2) (3) (-1) (3231564606451 / 10000000000000 : ℝ) (1615782303229 / 5000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hpsub_205 :
    IntervalIntegrable (fun t => Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1)) volume (32 / 15 : ℝ) (97 / 45 : ℝ) ∧
      (292015209 / 5000000000000 : ℝ) ≤ ∫ t in (32 / 15 : ℝ)..(97 / 45 : ℝ), Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1) :=
  quad_prod_log_div_sub (11 / 5 : ℝ) (198 / 193 : ℝ) (373 / 270 : ℝ) (32 / 15 : ℝ) (97 / 45 : ℝ) (193 / 90 : ℝ) (1 / 90 : ℝ)
    (90 / 193 : ℝ) (90 / 373 : ℝ) (90 / 283 : ℝ) (206633041676938971755323 / 25000000000000000000000000 : ℝ) (-7494773298534684559239245527023 / 50932217500000000000000000000000 : ℝ) (-3250729858557014560947034833796271277 / 103763631178692250000000000000000000000 : ℝ) (8237847440202058045831633920743937956639577 / 211396473271317401702575000000000000000000000 : ℝ)
    (63942104473 / 2500000000000 : ℝ) (255768417901 / 10000000000000 : ℝ) (3231564606451 / 10000000000000 : ℝ) (1615782303229 / 5000000000000 : ℝ) (292015209 / 5000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hlog_203 hlog_204 (by norm_num [quadProdLo])

private lemma hlog_206 : (19084340163 / 1250000000000 : ℝ) ≤ Real.log (66 / 65 : ℝ) ∧ Real.log (66 / 65 : ℝ) ≤ (4771085041 / 312500000000 : ℝ) :=
  log_rat_bounds (66 / 65 : ℝ) (1 / 703 : ℝ) (-4) (4) (-1) (19084340163 / 1250000000000 : ℝ) (4771085041 / 312500000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hlog_207 : (3285040669717 / 10000000000000 : ℝ) ≤ Real.log (25 / 18 : ℝ) ∧ Real.log (25 / 18 : ℝ) ≤ (3285040669723 / 10000000000000 : ℝ) :=
  log_rat_bounds (25 / 18 : ℝ) (0 : ℝ) (-1) (-2) (2) (3285040669717 / 10000000000000 : ℝ) (3285040669723 / 10000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hpsub_208 :
    IntervalIntegrable (fun t => Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1)) volume (97 / 45 : ℝ) (98 / 45 : ℝ) ∧
      (21992243 / 625000000000 : ℝ) ≤ ∫ t in (97 / 45 : ℝ)..(98 / 45 : ℝ), Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1) :=
  quad_prod_log_div_sub (11 / 5 : ℝ) (66 / 65 : ℝ) (25 / 18 : ℝ) (97 / 45 : ℝ) (98 / 45 : ℝ) (13 / 6 : ℝ) (1 / 90 : ℝ)
    (6 / 13 : ℝ) (6 / 25 : ℝ) (6 / 19 : ℝ) (62692833590168560943871 / 12500000000000000000000000 : ℝ) (-230847569803039623876810969 / 1543750000000000000000000000 : ℝ) (-5528589856385693167804372209 / 190653125000000000000000000000 : ℝ) (878638863804857710084610516151 / 23545660937500000000000000000000 : ℝ)
    (19084340163 / 1250000000000 : ℝ) (4771085041 / 312500000000 : ℝ) (3285040669717 / 10000000000000 : ℝ) (3285040669723 / 10000000000000 : ℝ) (21992243 / 625000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hlog_206 hlog_207 (by norm_num [quadProdLo])

private lemma hlog_209 : (10126603913 / 2000000000000 : ℝ) ≤ Real.log (198 / 197 : ℝ) ∧ Real.log (198 / 197 : ℝ) ≤ (25316509783 / 5000000000000 : ℝ) :=
  log_rat_bounds (198 / 197 : ℝ) (1 / 395 : ℝ) (0) (0) (0) (10126603913 / 2000000000000 : ℝ) (25316509783 / 5000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hlog_210 : (3338232284493 / 10000000000000 : ℝ) ≤ Real.log (377 / 270 : ℝ) ∧ Real.log (377 / 270 : ℝ) ≤ (3338232284499 / 10000000000000 : ℝ) :=
  log_rat_bounds (377 / 270 : ℝ) (1 / 376 : ℝ) (-1) (-2) (2) (3338232284493 / 10000000000000 : ℝ) (3338232284499 / 10000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hpsub_211 :
    IntervalIntegrable (fun t => Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1)) volume (98 / 45 : ℝ) (11 / 5 : ℝ) ∧
      (117710437 / 10000000000000 : ℝ) ≤ ∫ t in (98 / 45 : ℝ)..(11 / 5 : ℝ), Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1) :=
  quad_prod_log_div_sub (11 / 5 : ℝ) (198 / 197 : ℝ) (377 / 270 : ℝ) (98 / 45 : ℝ) (11 / 5 : ℝ) (197 / 90 : ℝ) (1 / 90 : ℝ)
    (90 / 197 : ℝ) (90 / 377 : ℝ) (90 / 287 : ℝ) (33804956114649743021109 / 20000000000000000000000000 : ℝ) (-6472547726391216591879912698889 / 42630406000000000000000000000000 : ℝ) (-2431472137991650905608868873895915731 / 90867575786241800000000000000000000000 : ℝ) (6921350168482005305080559809566381888830751 / 193686082400162857408540000000000000000000000 : ℝ)
    (10126603913 / 2000000000000 : ℝ) (25316509783 / 5000000000000 : ℝ) (3338232284493 / 10000000000000 : ℝ) (3338232284499 / 10000000000000 : ℝ) (117710437 / 10000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hlog_209 hlog_210 (by norm_num [quadProdLo])

private lemma hpchain_212 :
    IntervalIntegrable (fun t => Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1)) volume (1 : ℝ) (47 / 45 : ℝ) ∧
      (612879211 / 5000000000000 : ℝ) ≤ ∫ t in (1 : ℝ)..(47 / 45 : ℝ), Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1) :=
  chain_int_lb hpsub_52 hpsub_55 (by norm_num)

private lemma hpchain_213 :
    IntervalIntegrable (fun t => Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1)) volume (1 : ℝ) (16 / 15 : ℝ) ∧
      (1340285743 / 5000000000000 : ℝ) ≤ ∫ t in (1 : ℝ)..(16 / 15 : ℝ), Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1) :=
  chain_int_lb hpchain_212 hpsub_58 (by norm_num)

private lemma hpchain_214 :
    IntervalIntegrable (fun t => Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1)) volume (1 : ℝ) (49 / 45 : ℝ) ∧
      (289503473 / 625000000000 : ℝ) ≤ ∫ t in (1 : ℝ)..(49 / 45 : ℝ), Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1) :=
  chain_int_lb hpchain_213 hpsub_61 (by norm_num)

private lemma hpchain_215 :
    IntervalIntegrable (fun t => Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1)) volume (1 : ℝ) (10 / 9 : ℝ) ∧
      (3517697839 / 5000000000000 : ℝ) ≤ ∫ t in (1 : ℝ)..(10 / 9 : ℝ), Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1) :=
  chain_int_lb hpchain_214 hpsub_64 (by norm_num)

private lemma hpchain_216 :
    IntervalIntegrable (fun t => Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1)) volume (1 : ℝ) (17 / 15 : ℝ) ∧
      (9848461583 / 10000000000000 : ℝ) ≤ ∫ t in (1 : ℝ)..(17 / 15 : ℝ), Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1) :=
  chain_int_lb hpchain_215 hpsub_67 (by norm_num)

private lemma hpchain_217 :
    IntervalIntegrable (fun t => Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1)) volume (1 : ℝ) (52 / 45 : ℝ) ∧
      (13031630471 / 10000000000000 : ℝ) ≤ ∫ t in (1 : ℝ)..(52 / 45 : ℝ), Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1) :=
  chain_int_lb hpchain_216 hpsub_70 (by norm_num)

private lemma hpchain_218 :
    IntervalIntegrable (fun t => Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1)) volume (1 : ℝ) (53 / 45 : ℝ) ∧
      (1654762327 / 1000000000000 : ℝ) ≤ ∫ t in (1 : ℝ)..(53 / 45 : ℝ), Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1) :=
  chain_int_lb hpchain_217 hpsub_73 (by norm_num)

private lemma hpchain_219 :
    IntervalIntegrable (fun t => Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1)) volume (1 : ℝ) (6 / 5 : ℝ) ∧
      (318146147 / 156250000000 : ℝ) ≤ ∫ t in (1 : ℝ)..(6 / 5 : ℝ), Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1) :=
  chain_int_lb hpchain_218 hpsub_76 (by norm_num)

private lemma hpchain_220 :
    IntervalIntegrable (fun t => Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1)) volume (1 : ℝ) (11 / 9 : ℝ) ∧
      (3054973363 / 1250000000000 : ℝ) ≤ ∫ t in (1 : ℝ)..(11 / 9 : ℝ), Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1) :=
  chain_int_lb hpchain_219 hpsub_79 (by norm_num)

private lemma hpchain_221 :
    IntervalIntegrable (fun t => Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1)) volume (1 : ℝ) (56 / 45 : ℝ) ∧
      (28751812799 / 10000000000000 : ℝ) ≤ ∫ t in (1 : ℝ)..(56 / 45 : ℝ), Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1) :=
  chain_int_lb hpchain_220 hpsub_82 (by norm_num)

private lemma hpchain_222 :
    IntervalIntegrable (fun t => Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1)) volume (1 : ℝ) (19 / 15 : ℝ) ∧
      (16634061519 / 5000000000000 : ℝ) ≤ ∫ t in (1 : ℝ)..(19 / 15 : ℝ), Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1) :=
  chain_int_lb hpchain_221 hpsub_85 (by norm_num)

private lemma hpchain_223 :
    IntervalIntegrable (fun t => Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1)) volume (1 : ℝ) (58 / 45 : ℝ) ∧
      (37961101007 / 10000000000000 : ℝ) ≤ ∫ t in (1 : ℝ)..(58 / 45 : ℝ), Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1) :=
  chain_int_lb hpchain_222 hpsub_88 (by norm_num)

private lemma hpchain_224 :
    IntervalIntegrable (fun t => Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1)) volume (1 : ℝ) (59 / 45 : ℝ) ∧
      (8560943599 / 2000000000000 : ℝ) ≤ ∫ t in (1 : ℝ)..(59 / 45 : ℝ), Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1) :=
  chain_int_lb hpchain_223 hpsub_91 (by norm_num)

private lemma hpchain_225 :
    IntervalIntegrable (fun t => Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1)) volume (1 : ℝ) (4 / 3 : ℝ) ∧
      (47774436929 / 10000000000000 : ℝ) ≤ ∫ t in (1 : ℝ)..(4 / 3 : ℝ), Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1) :=
  chain_int_lb hpchain_224 hpsub_94 (by norm_num)

private lemma hpchain_226 :
    IntervalIntegrable (fun t => Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1)) volume (1 : ℝ) (61 / 45 : ℝ) ∧
      (52847122793 / 10000000000000 : ℝ) ≤ ∫ t in (1 : ℝ)..(61 / 45 : ℝ), Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1) :=
  chain_int_lb hpchain_225 hpsub_97 (by norm_num)

private lemma hpchain_227 :
    IntervalIntegrable (fun t => Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1)) volume (1 : ℝ) (62 / 45 : ℝ) ∧
      (11600191839 / 2000000000000 : ℝ) ≤ ∫ t in (1 : ℝ)..(62 / 45 : ℝ), Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1) :=
  chain_int_lb hpchain_226 hpsub_100 (by norm_num)

private lemma hpchain_228 :
    IntervalIntegrable (fun t => Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1)) volume (1 : ℝ) (7 / 5 : ℝ) ∧
      (1975480331 / 312500000000 : ℝ) ≤ ∫ t in (1 : ℝ)..(7 / 5 : ℝ), Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1) :=
  chain_int_lb hpchain_227 hpsub_103 (by norm_num)

private lemma hpchain_229 :
    IntervalIntegrable (fun t => Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1)) volume (1 : ℝ) (64 / 45 : ℝ) ∧
      (68470949733 / 10000000000000 : ℝ) ≤ ∫ t in (1 : ℝ)..(64 / 45 : ℝ), Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1) :=
  chain_int_lb hpchain_228 hpsub_106 (by norm_num)

private lemma hpchain_230 :
    IntervalIntegrable (fun t => Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1)) volume (1 : ℝ) (13 / 9 : ℝ) ∧
      (18437347479 / 2500000000000 : ℝ) ≤ ∫ t in (1 : ℝ)..(13 / 9 : ℝ), Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1) :=
  chain_int_lb hpchain_229 hpsub_109 (by norm_num)

private lemma hpchain_231 :
    IntervalIntegrable (fun t => Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1)) volume (1 : ℝ) (22 / 15 : ℝ) ∧
      (19758355423 / 2500000000000 : ℝ) ≤ ∫ t in (1 : ℝ)..(22 / 15 : ℝ), Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1) :=
  chain_int_lb hpchain_230 hpsub_112 (by norm_num)

private lemma hpchain_232 :
    IntervalIntegrable (fun t => Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1)) volume (1 : ℝ) (67 / 45 : ℝ) ∧
      (84306753683 / 10000000000000 : ℝ) ≤ ∫ t in (1 : ℝ)..(67 / 45 : ℝ), Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1) :=
  chain_int_lb hpchain_231 hpsub_115 (by norm_num)

private lemma hpchain_233 :
    IntervalIntegrable (fun t => Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1)) volume (1 : ℝ) (68 / 45 : ℝ) ∧
      (89554017203 / 10000000000000 : ℝ) ≤ ∫ t in (1 : ℝ)..(68 / 45 : ℝ), Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1) :=
  chain_int_lb hpchain_232 hpsub_118 (by norm_num)

private lemma hpchain_234 :
    IntervalIntegrable (fun t => Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1)) volume (1 : ℝ) (23 / 15 : ℝ) ∧
      (47380357203 / 5000000000000 : ℝ) ≤ ∫ t in (1 : ℝ)..(23 / 15 : ℝ), Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1) :=
  chain_int_lb hpchain_233 hpsub_121 (by norm_num)

private lemma hpchain_235 :
    IntervalIntegrable (fun t => Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1)) volume (1 : ℝ) (14 / 9 : ℝ) ∧
      (99913169703 / 10000000000000 : ℝ) ≤ ∫ t in (1 : ℝ)..(14 / 9 : ℝ), Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1) :=
  chain_int_lb hpchain_234 hpsub_124 (by norm_num)

private lemma hpchain_236 :
    IntervalIntegrable (fun t => Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1)) volume (1 : ℝ) (71 / 45 : ℝ) ∧
      (104998484213 / 10000000000000 : ℝ) ≤ ∫ t in (1 : ℝ)..(71 / 45 : ℝ), Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1) :=
  chain_int_lb hpchain_235 hpsub_127 (by norm_num)

private lemma hpchain_237 :
    IntervalIntegrable (fun t => Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1)) volume (1 : ℝ) (8 / 5 : ℝ) ∧
      (27501123257 / 2500000000000 : ℝ) ≤ ∫ t in (1 : ℝ)..(8 / 5 : ℝ), Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1) :=
  chain_int_lb hpchain_236 hpsub_130 (by norm_num)

private lemma hpchain_238 :
    IntervalIntegrable (fun t => Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1)) volume (1 : ℝ) (73 / 45 : ℝ) ∧
      (57459862551 / 5000000000000 : ℝ) ≤ ∫ t in (1 : ℝ)..(73 / 45 : ℝ), Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1) :=
  chain_int_lb hpchain_237 hpsub_133 (by norm_num)

private lemma hpchain_239 :
    IntervalIntegrable (fun t => Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1)) volume (1 : ℝ) (74 / 45 : ℝ) ∧
      (11973336557 / 1000000000000 : ℝ) ≤ ∫ t in (1 : ℝ)..(74 / 45 : ℝ), Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1) :=
  chain_int_lb hpchain_238 hpsub_136 (by norm_num)

private lemma hpchain_240 :
    IntervalIntegrable (fun t => Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1)) volume (1 : ℝ) (5 / 3 : ℝ) ∧
      (124435220341 / 10000000000000 : ℝ) ≤ ∫ t in (1 : ℝ)..(5 / 3 : ℝ), Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1) :=
  chain_int_lb hpchain_239 hpsub_139 (by norm_num)

private lemma hpchain_241 :
    IntervalIntegrable (fun t => Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1)) volume (1 : ℝ) (76 / 45 : ℝ) ∧
      (129015682801 / 10000000000000 : ℝ) ≤ ∫ t in (1 : ℝ)..(76 / 45 : ℝ), Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1) :=
  chain_int_lb hpchain_240 hpsub_142 (by norm_num)

private lemma hpchain_242 :
    IntervalIntegrable (fun t => Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1)) volume (1 : ℝ) (77 / 45 : ℝ) ∧
      (66732851243 / 5000000000000 : ℝ) ≤ ∫ t in (1 : ℝ)..(77 / 45 : ℝ), Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1) :=
  chain_int_lb hpchain_241 hpsub_145 (by norm_num)

private lemma hpchain_243 :
    IntervalIntegrable (fun t => Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1)) volume (1 : ℝ) (26 / 15 : ℝ) ∧
      (17222094449 / 1250000000000 : ℝ) ≤ ∫ t in (1 : ℝ)..(26 / 15 : ℝ), Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1) :=
  chain_int_lb hpchain_242 hpsub_148 (by norm_num)

private lemma hpchain_244 :
    IntervalIntegrable (fun t => Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1)) volume (1 : ℝ) (79 / 45 : ℝ) ∧
      (28388163441 / 2000000000000 : ℝ) ≤ ∫ t in (1 : ℝ)..(79 / 45 : ℝ), Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1) :=
  chain_int_lb hpchain_243 hpsub_151 (by norm_num)

private lemma hpchain_245 :
    IntervalIntegrable (fun t => Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1)) volume (1 : ℝ) (16 / 9 : ℝ) ∧
      (14595033513 / 1000000000000 : ℝ) ≤ ∫ t in (1 : ℝ)..(16 / 9 : ℝ), Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1) :=
  chain_int_lb hpchain_244 hpsub_154 (by norm_num)

private lemma hpchain_246 :
    IntervalIntegrable (fun t => Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1)) volume (1 : ℝ) (9 / 5 : ℝ) ∧
      (74899102611 / 5000000000000 : ℝ) ≤ ∫ t in (1 : ℝ)..(9 / 5 : ℝ), Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1) :=
  chain_int_lb hpchain_245 hpsub_157 (by norm_num)

private lemma hpchain_247 :
    IntervalIntegrable (fun t => Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1)) volume (1 : ℝ) (82 / 45 : ℝ) ∧
      (38369437029 / 2500000000000 : ℝ) ≤ ∫ t in (1 : ℝ)..(82 / 45 : ℝ), Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1) :=
  chain_int_lb hpchain_246 hpsub_160 (by norm_num)

private lemma hpchain_248 :
    IntervalIntegrable (fun t => Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1)) volume (1 : ℝ) (83 / 45 : ℝ) ∧
      (19622835909 / 1250000000000 : ℝ) ≤ ∫ t in (1 : ℝ)..(83 / 45 : ℝ), Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1) :=
  chain_int_lb hpchain_247 hpsub_163 (by norm_num)

private lemma hpchain_249 :
    IntervalIntegrable (fun t => Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1)) volume (1 : ℝ) (28 / 15 : ℝ) ∧
      (20038391031 / 1250000000000 : ℝ) ≤ ∫ t in (1 : ℝ)..(28 / 15 : ℝ), Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1) :=
  chain_int_lb hpchain_248 hpsub_166 (by norm_num)

private lemma hpchain_250 :
    IntervalIntegrable (fun t => Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1)) volume (1 : ℝ) (17 / 9 : ℝ) ∧
      (40861384781 / 2500000000000 : ℝ) ≤ ∫ t in (1 : ℝ)..(17 / 9 : ℝ), Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1) :=
  chain_int_lb hpchain_249 hpsub_169 (by norm_num)

private lemma hpchain_251 :
    IntervalIntegrable (fun t => Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1)) volume (1 : ℝ) (86 / 45 : ℝ) ∧
      (166392732009 / 10000000000000 : ℝ) ≤ ∫ t in (1 : ℝ)..(86 / 45 : ℝ), Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1) :=
  chain_int_lb hpchain_250 hpsub_172 (by norm_num)

private lemma hpchain_252 :
    IntervalIntegrable (fun t => Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1)) volume (1 : ℝ) (29 / 15 : ℝ) ∧
      (84571922779 / 5000000000000 : ℝ) ≤ ∫ t in (1 : ℝ)..(29 / 15 : ℝ), Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1) :=
  chain_int_lb hpchain_251 hpsub_175 (by norm_num)

private lemma hpchain_253 :
    IntervalIntegrable (fun t => Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1)) volume (1 : ℝ) (88 / 45 : ℝ) ∧
      (85847164221 / 5000000000000 : ℝ) ≤ ∫ t in (1 : ℝ)..(88 / 45 : ℝ), Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1) :=
  chain_int_lb hpchain_252 hpsub_178 (by norm_num)

private lemma hpchain_254 :
    IntervalIntegrable (fun t => Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1)) volume (1 : ℝ) (89 / 45 : ℝ) ∧
      (174039923711 / 10000000000000 : ℝ) ≤ ∫ t in (1 : ℝ)..(89 / 45 : ℝ), Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1) :=
  chain_int_lb hpchain_253 hpsub_181 (by norm_num)

private lemma hpchain_255 :
    IntervalIntegrable (fun t => Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1)) volume (1 : ℝ) (2 : ℝ) ∧
      (35235330799 / 2000000000000 : ℝ) ≤ ∫ t in (1 : ℝ)..(2 : ℝ), Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1) :=
  chain_int_lb hpchain_254 hpsub_184 (by norm_num)

private lemma hpchain_256 :
    IntervalIntegrable (fun t => Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1)) volume (1 : ℝ) (91 / 45 : ℝ) ∧
      (71240323 / 4000000000 : ℝ) ≤ ∫ t in (1 : ℝ)..(91 / 45 : ℝ), Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1) :=
  chain_int_lb hpchain_255 hpsub_187 (by norm_num)

private lemma hpchain_257 :
    IntervalIntegrable (fun t => Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1)) volume (1 : ℝ) (92 / 45 : ℝ) ∧
      (179808924737 / 10000000000000 : ℝ) ≤ ∫ t in (1 : ℝ)..(92 / 45 : ℝ), Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1) :=
  chain_int_lb hpchain_256 hpsub_190 (by norm_num)

private lemma hpchain_258 :
    IntervalIntegrable (fun t => Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1)) volume (1 : ℝ) (31 / 15 : ℝ) ∧
      (181297785959 / 10000000000000 : ℝ) ≤ ∫ t in (1 : ℝ)..(31 / 15 : ℝ), Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1) :=
  chain_int_lb hpchain_257 hpsub_193 (by norm_num)

private lemma hpchain_259 :
    IntervalIntegrable (fun t => Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1)) volume (1 : ℝ) (94 / 45 : ℝ) ∧
      (11410274953 / 625000000000 : ℝ) ≤ ∫ t in (1 : ℝ)..(94 / 45 : ℝ), Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1) :=
  chain_int_lb hpchain_258 hpsub_196 (by norm_num)

private lemma hpchain_260 :
    IntervalIntegrable (fun t => Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1)) volume (1 : ℝ) (19 / 9 : ℝ) ∧
      (45901497307 / 2500000000000 : ℝ) ≤ ∫ t in (1 : ℝ)..(19 / 9 : ℝ), Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1) :=
  chain_int_lb hpchain_259 hpsub_199 (by norm_num)

private lemma hpchain_261 :
    IntervalIntegrable (fun t => Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1)) volume (1 : ℝ) (32 / 15 : ℝ) ∧
      (184419986357 / 10000000000000 : ℝ) ≤ ∫ t in (1 : ℝ)..(32 / 15 : ℝ), Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1) :=
  chain_int_lb hpchain_260 hpsub_202 (by norm_num)

private lemma hpchain_262 :
    IntervalIntegrable (fun t => Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1)) volume (1 : ℝ) (97 / 45 : ℝ) ∧
      (7400160671 / 400000000000 : ℝ) ≤ ∫ t in (1 : ℝ)..(97 / 45 : ℝ), Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1) :=
  chain_int_lb hpchain_261 hpsub_205 (by norm_num)

private lemma hpchain_263 :
    IntervalIntegrable (fun t => Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1)) volume (1 : ℝ) (98 / 45 : ℝ) ∧
      (185355892663 / 10000000000000 : ℝ) ≤ ∫ t in (1 : ℝ)..(98 / 45 : ℝ), Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1) :=
  chain_int_lb hpchain_262 hpsub_208 (by norm_num)

private lemma hpchain_264 :
    IntervalIntegrable (fun t => Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1)) volume (1 : ℝ) (11 / 5 : ℝ) ∧
      (1854736031 / 100000000000 : ℝ) ≤ ∫ t in (1 : ℝ)..(11 / 5 : ℝ), Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1) :=
  chain_int_lb hpchain_263 hpsub_211 (by norm_num)

private lemma hlog_265 : (17751536095797 / 5000000000000 : ℝ) ≤ Real.log (800000000 / 22972653 : ℝ) ∧ Real.log (800000000 / 22972653 : ℝ) ≤ (8875768047901 / 2500000000000 : ℝ) :=
  log_rat_bounds (800000000 / 22972653 : ℝ) (4738369 / 1245261631 : ℝ) (5) (3) (-2) (17751536095797 / 5000000000000 : ℝ) (8875768047901 / 2500000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hterm_s0_266 :
    IntervalIntegrable (fun t => sigma0 t / ((5 : ℝ) * t) * Real.log (800000000 / 22972653 : ℝ)) volume (1 : ℝ) (11 / 5 : ℝ) ∧
      (158996267243 / 10000000000000 : ℝ) ≤ ∫ t in (1 : ℝ)..(11 / 5 : ℝ), sigma0 t / ((5 : ℝ) * t) * Real.log (800000000 / 22972653 : ℝ) :=
  bound_sigma0_term (5 : ℝ) (800000000 / 22972653 : ℝ) (1 : ℝ) (11 / 5 : ℝ) (11 / 5 : ℝ)
    (85846709821 / 500000000000 : ℝ) (1716934197987 / 10000000000000 : ℝ) (0 : ℝ) (7884573603639 / 10000000000000 : ℝ) (3942286801823 / 5000000000000 : ℝ) (1854736031 / 100000000000 : ℝ) (17751536095797 / 5000000000000 : ℝ) (8875768047901 / 2500000000000 : ℝ) (158996267243 / 10000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hqchain_47 (by norm_num) hfga_48 hlog_49 hpchain_264.2 hlog_265
    (by norm_num) (by norm_num) (by norm_num)

private lemma hterm_267 :
    IntervalIntegrable (fun t => ind (127 / 50 : ℝ) (3 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) ^ (5 : ℕ) / (22972653 / 781250 : ℝ))) volume (1 : ℝ) (11 / 5 : ℝ) ∧
      (0 : ℝ) ≤ ∫ t in (1 : ℝ)..(11 / 5 : ℝ), ind (127 / 50 : ℝ) (3 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) ^ (5 : ℕ) / (22972653 / 781250 : ℝ)) :=
  bound_ind_div_zero (1 : ℝ) (11 / 5 : ℝ) (127 / 50 : ℝ) (3 : ℝ) (fun t => (5 : ℝ) * t) (fun t => (t + 1) ^ (5 : ℕ) / (22972653 / 781250 : ℝ)) (by norm_num) (Or.inr (by norm_num))

private lemma hlog_269 : (6418538861721 / 10000000000000 : ℝ) ≤ Real.log (19 / 10 : ℝ) ∧ Real.log (19 / 10 : ℝ) ≤ (3209269430863 / 5000000000000 : ℝ) :=
  log_rat_bounds (19 / 10 : ℝ) (1 / 151 : ℝ) (-3) (1) (1) (6418538861721 / 10000000000000 : ℝ) (3209269430863 / 5000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hlog_270 : (1531369949959 / 10000000000000 : ℝ) ≤ Real.log (493 / 423 : ℝ) ∧ Real.log (493 / 423 : ℝ) ≤ (1531369949969 / 10000000000000 : ℝ) :=
  log_rat_bounds (493 / 423 : ℝ) (41 / 11791 : ℝ) (-2) (-3) (3) (1531369949959 / 10000000000000 : ℝ) (1531369949969 / 10000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hlog_271 : (8616524663627 / 10000000000000 : ℝ) ≤ Real.log (13729 / 5800 : ℝ) ∧ Real.log (13729 / 5800 : ℝ) ≤ (1723304932727 / 2000000000000 : ℝ) :=
  log_rat_bounds (13729 / 5800 : ℝ) (541 / 109291 : ℝ) (-5) (1) (2) (8616524663627 / 10000000000000 : ℝ) (1723304932727 / 2000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hqsub_272 :
    IntervalIntegrable (fun t => Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t)) volume (3807 / 2900 : ℝ) (2061 / 1450 : ℝ) ∧
      (136935288711 / 2000000000000 : ℝ) ≤ ∫ t in (3807 / 2900 : ℝ)..(2061 / 1450 : ℝ), Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (3807 / 2900 : ℝ)..(2061 / 1450 : ℝ), Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ≤ (171169111777 / 2500000000000 : ℝ) :=
  quad_log_div_sub (1 : ℝ) (1 : ℝ) (0 : ℝ) (1 : ℝ) (3807 / 2900 : ℝ) (2061 / 1450 : ℝ) (7929 / 5800 : ℝ) (63 / 1160 : ℝ)
    (13729 / 5800 : ℝ) (7929 / 5800 : ℝ) (5800 / 13729 : ℝ) (5800 / 7929 : ℝ) (5800 / 7929 : ℝ) (8616524663627 / 10000000000000 : ℝ) (1723304932727 / 2000000000000 : ℝ) (136935288711 / 2000000000000 : ℝ) (171169111777 / 2500000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog_271 (by norm_num [quadLogLo]) (by norm_num [quadLogHi])

private lemma hlog_273 : (9065190057593 / 10000000000000 : ℝ) ≤ Real.log (14359 / 5800 : ℝ) ∧ Real.log (14359 / 5800 : ℝ) ≤ (9065190057603 / 10000000000000 : ℝ) :=
  log_rat_bounds (14359 / 5800 : ℝ) (3079 / 2323079 : ℝ) (3) (-4) (2) (9065190057593 / 10000000000000 : ℝ) (9065190057603 / 10000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hqsub_274 :
    IntervalIntegrable (fun t => Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t)) volume (2061 / 1450 : ℝ) (153 / 100 : ℝ) ∧
      (333651567181 / 5000000000000 : ℝ) ≤ ∫ t in (2061 / 1450 : ℝ)..(153 / 100 : ℝ), Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (2061 / 1450 : ℝ)..(153 / 100 : ℝ), Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ≤ (83412892057 / 1250000000000 : ℝ) :=
  quad_log_div_sub (1 : ℝ) (1 : ℝ) (0 : ℝ) (1 : ℝ) (2061 / 1450 : ℝ) (153 / 100 : ℝ) (8559 / 5800 : ℝ) (63 / 1160 : ℝ)
    (14359 / 5800 : ℝ) (8559 / 5800 : ℝ) (5800 / 14359 : ℝ) (5800 / 8559 : ℝ) (5800 / 8559 : ℝ) (9065190057593 / 10000000000000 : ℝ) (9065190057603 / 10000000000000 : ℝ) (333651567181 / 5000000000000 : ℝ) (83412892057 / 1250000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog_273 (by norm_num [quadLogLo]) (by norm_num [quadLogHi])

private lemma hqchain_275 :
    IntervalIntegrable (fun t => Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t)) volume (3807 / 2900 : ℝ) (153 / 100 : ℝ) ∧
      (1351979577917 / 10000000000000 : ℝ) ≤ ∫ t in (3807 / 2900 : ℝ)..(153 / 100 : ℝ), Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (3807 / 2900 : ℝ)..(153 / 100 : ℝ), Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ≤ (337994895891 / 2500000000000 : ℝ) :=
  chain_int_bounds hqsub_272 hqsub_274 (by norm_num) (by norm_num)

private lemma hlog_276 : (1509435721069 / 10000000000000 : ℝ) ≤ Real.log (1349 / 1160 : ℝ) ∧ Real.log (1349 / 1160 : ℝ) ≤ (754717860539 / 5000000000000 : ℝ) :=
  log_rat_bounds (1349 / 1160 : ℝ) (173 / 72673 : ℝ) (-2) (-3) (3) (1509435721069 / 10000000000000 : ℝ) (754717860539 / 5000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hqsub_277 :
    IntervalIntegrable (fun t => Real.log ((253 / 100 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t)) volume (3807 / 2900 : ℝ) (2061 / 1450 : ℝ) ∧
      (7512399769 / 625000000000 : ℝ) ≤ ∫ t in (3807 / 2900 : ℝ)..(2061 / 1450 : ℝ), Real.log ((253 / 100 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (3807 / 2900 : ℝ)..(2061 / 1450 : ℝ), Real.log ((253 / 100 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ≤ (120198404623 / 10000000000000 : ℝ) :=
  quad_log_div_sub (253 / 100 : ℝ) (-1 : ℝ) (0 : ℝ) (1 : ℝ) (3807 / 2900 : ℝ) (2061 / 1450 : ℝ) (7929 / 5800 : ℝ) (63 / 1160 : ℝ)
    (1349 / 1160 : ℝ) (7929 / 5800 : ℝ) (-1160 / 1349 : ℝ) (5800 / 7929 : ℝ) (1160 / 1349 : ℝ) (1509435721069 / 10000000000000 : ℝ) (754717860539 / 5000000000000 : ℝ) (7512399769 / 625000000000 : ℝ) (120198404623 / 10000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog_276 (by norm_num [quadLogLo]) (by norm_num [quadLogHi])

private lemma hlog_278 : (66108564483 / 1250000000000 : ℝ) ≤ Real.log (1223 / 1160 : ℝ) ∧ Real.log (1223 / 1160 : ℝ) ≤ (528868515871 / 10000000000000 : ℝ) :=
  log_rat_bounds (1223 / 1160 : ℝ) (22 / 3647 : ℝ) (-3) (-1) (2) (66108564483 / 1250000000000 : ℝ) (528868515871 / 10000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hqsub_279 :
    IntervalIntegrable (fun t => Real.log ((253 / 100 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t)) volume (2061 / 1450 : ℝ) (153 / 100 : ℝ) ∧
      (39085589109 / 10000000000000 : ℝ) ≤ ∫ t in (2061 / 1450 : ℝ)..(153 / 100 : ℝ), Real.log ((253 / 100 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (2061 / 1450 : ℝ)..(153 / 100 : ℝ), Real.log ((253 / 100 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ≤ (39085602879 / 10000000000000 : ℝ) :=
  quad_log_div_sub (253 / 100 : ℝ) (-1 : ℝ) (0 : ℝ) (1 : ℝ) (2061 / 1450 : ℝ) (153 / 100 : ℝ) (8559 / 5800 : ℝ) (63 / 1160 : ℝ)
    (1223 / 1160 : ℝ) (8559 / 5800 : ℝ) (-1160 / 1223 : ℝ) (5800 / 8559 : ℝ) (1160 / 1223 : ℝ) (66108564483 / 1250000000000 : ℝ) (528868515871 / 10000000000000 : ℝ) (39085589109 / 10000000000000 : ℝ) (39085602879 / 10000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog_278 (by norm_num [quadLogLo]) (by norm_num [quadLogHi])

private lemma hqchain_280 :
    IntervalIntegrable (fun t => Real.log ((253 / 100 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t)) volume (3807 / 2900 : ℝ) (153 / 100 : ℝ) ∧
      (159283985413 / 10000000000000 : ℝ) ≤ ∫ t in (3807 / 2900 : ℝ)..(153 / 100 : ℝ), Real.log ((253 / 100 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (3807 / 2900 : ℝ)..(153 / 100 : ℝ), Real.log ((253 / 100 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ≤ (79642003751 / 5000000000000 : ℝ) :=
  chain_int_bounds hqsub_277 hqsub_279 (by norm_num) (by norm_num)

private lemma hact_tl_281 :
    IntervalIntegrable (fun t => Real.log ((t + 1) / ((19 / 10 : ℝ) * ((253 / 100 : ℝ) - t))) / ((5 : ℝ) * t)) volume (3807 / 2900 : ℝ) (153 / 100 : ℝ) ∧
      (41955963371 / 10000000000000 : ℝ) ≤ ∫ t in (3807 / 2900 : ℝ)..(153 / 100 : ℝ), Real.log ((t + 1) / ((19 / 10 : ℝ) * ((253 / 100 : ℝ) - t))) / ((5 : ℝ) * t) :=
  active_t_lin (5 : ℝ) (19 / 10 : ℝ) (253 / 100 : ℝ) (3807 / 2900 : ℝ) (153 / 100 : ℝ) (493 / 423 : ℝ) (6418538861721 / 10000000000000 : ℝ) (3209269430863 / 5000000000000 : ℝ) (1531369949959 / 10000000000000 : ℝ) (1531369949969 / 10000000000000 : ℝ)
    (1351979577917 / 10000000000000 : ℝ) (337994895891 / 2500000000000 : ℝ) (159283985413 / 10000000000000 : ℝ) (79642003751 / 5000000000000 : ℝ) (41955963371 / 10000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog_269 hlog_270 hqchain_275 hqchain_280 (by norm_num)

private lemma hterm_268 :
    IntervalIntegrable (fun t => ind (3807 / 2900 : ℝ) (153 / 100 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) / ((19 / 10 : ℝ) * ((253 / 100 : ℝ) - t)))) volume (1 : ℝ) (11 / 5 : ℝ) ∧
      (41955963371 / 10000000000000 : ℝ) ≤ ∫ t in (1 : ℝ)..(11 / 5 : ℝ), ind (3807 / 2900 : ℝ) (153 / 100 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) / ((19 / 10 : ℝ) * ((253 / 100 : ℝ) - t))) :=
  bound_ind_div_active (1 : ℝ) (11 / 5 : ℝ) (3807 / 2900 : ℝ) (153 / 100 : ℝ) (3807 / 2900 : ℝ) (153 / 100 : ℝ) (41955963371 / 10000000000000 : ℝ)
    (fun t => (5 : ℝ) * t) (fun t => (t + 1) / ((19 / 10 : ℝ) * ((253 / 100 : ℝ) - t)))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (Or.inr rfl) (Or.inr rfl) hact_tl_281

private lemma hlog_283 : (29171449087 / 80000000000 : ℝ) ≤ Real.log (36 / 25 : ℝ) ∧ Real.log (36 / 25 : ℝ) ≤ (1823215567941 / 5000000000000 : ℝ) :=
  log_rat_bounds (36 / 25 : ℝ) (0 : ℝ) (2) (2) (-2) (29171449087 / 80000000000 : ℝ) (1823215567941 / 5000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hlog_284 : (1350269816029 / 5000000000000 : ℝ) ≤ Real.log (3355 / 2561 : ℝ) ∧ Real.log (3355 / 2561 : ℝ) ≤ (2700539632067 / 10000000000000 : ℝ) :=
  log_rat_bounds (3355 / 2561 : ℝ) (391 / 128441 : ℝ) (-5) (-1) (3) (1350269816029 / 5000000000000 : ℝ) (2700539632067 / 10000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hlog_285 : (10048178993631 / 10000000000000 : ℝ) ≤ Real.log (20827 / 7625 : ℝ) ∧ Real.log (20827 / 7625 : ℝ) ≤ (10048178993637 / 10000000000000 : ℝ) :=
  log_rat_bounds (20827 / 7625 : ℝ) (479 / 82829 : ℝ) (-1) (3) (-1) (10048178993631 / 10000000000000 : ℝ) (10048178993637 / 10000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hqsub_286 :
    IntervalIntegrable (fun t => Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t)) volume (2561 / 1525 : ℝ) (13599 / 7625 : ℝ) ∧
      (302176226807 / 5000000000000 : ℝ) ≤ ∫ t in (2561 / 1525 : ℝ)..(13599 / 7625 : ℝ), Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (2561 / 1525 : ℝ)..(13599 / 7625 : ℝ), Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ≤ (604352454131 / 10000000000000 : ℝ) :=
  quad_log_div_sub (1 : ℝ) (1 : ℝ) (0 : ℝ) (1 : ℝ) (2561 / 1525 : ℝ) (13599 / 7625 : ℝ) (13202 / 7625 : ℝ) (397 / 7625 : ℝ)
    (20827 / 7625 : ℝ) (13202 / 7625 : ℝ) (7625 / 20827 : ℝ) (7625 / 13202 : ℝ) (7625 / 13202 : ℝ) (10048178993631 / 10000000000000 : ℝ) (10048178993637 / 10000000000000 : ℝ) (302176226807 / 5000000000000 : ℝ) (604352454131 / 10000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog_285 (by norm_num [quadLogLo]) (by norm_num [quadLogHi])

private lemma hlog_287 : (5211163710583 / 5000000000000 : ℝ) ≤ Real.log (21621 / 7625 : ℝ) ∧ Real.log (21621 / 7625 : ℝ) ≤ (2605581855293 / 2500000000000 : ℝ) :=
  log_rat_bounds (21621 / 7625 : ℝ) (937 / 229687 : ℝ) (-4) (2) (1) (5211163710583 / 5000000000000 : ℝ) (2605581855293 / 2500000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hqsub_288 :
    IntervalIntegrable (fun t => Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t)) volume (13599 / 7625 : ℝ) (14393 / 7625 : ℝ) ∧
      (591291996431 / 10000000000000 : ℝ) ≤ ∫ t in (13599 / 7625 : ℝ)..(14393 / 7625 : ℝ), Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (13599 / 7625 : ℝ)..(14393 / 7625 : ℝ), Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ≤ (591291996777 / 10000000000000 : ℝ) :=
  quad_log_div_sub (1 : ℝ) (1 : ℝ) (0 : ℝ) (1 : ℝ) (13599 / 7625 : ℝ) (14393 / 7625 : ℝ) (13996 / 7625 : ℝ) (397 / 7625 : ℝ)
    (21621 / 7625 : ℝ) (13996 / 7625 : ℝ) (7625 / 21621 : ℝ) (7625 / 13996 : ℝ) (7625 / 13996 : ℝ) (5211163710583 / 5000000000000 : ℝ) (2605581855293 / 2500000000000 : ℝ) (591291996431 / 10000000000000 : ℝ) (591291996777 / 10000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog_287 (by norm_num [quadLogLo]) (by norm_num [quadLogHi])

private lemma hlog_289 : (5391490275567 / 5000000000000 : ℝ) ≤ Real.log (4483 / 1525 : ℝ) ∧ Real.log (4483 / 1525 : ℝ) ≤ (1347872568893 / 1250000000000 : ℝ) :=
  log_rat_bounds (4483 / 1525 : ℝ) (1949 / 1145699 : ℝ) (-7) (1) (3) (5391490275567 / 5000000000000 : ℝ) (1347872568893 / 1250000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hqsub_290 :
    IntervalIntegrable (fun t => Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t)) volume (14393 / 7625 : ℝ) (15187 / 7625 : ℝ) ∧
      (289454682157 / 5000000000000 : ℝ) ≤ ∫ t in (14393 / 7625 : ℝ)..(15187 / 7625 : ℝ), Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (14393 / 7625 : ℝ)..(15187 / 7625 : ℝ), Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ≤ (578909364551 / 10000000000000 : ℝ) :=
  quad_log_div_sub (1 : ℝ) (1 : ℝ) (0 : ℝ) (1 : ℝ) (14393 / 7625 : ℝ) (15187 / 7625 : ℝ) (2958 / 1525 : ℝ) (397 / 7625 : ℝ)
    (4483 / 1525 : ℝ) (2958 / 1525 : ℝ) (1525 / 4483 : ℝ) (1525 / 2958 : ℝ) (1525 / 2958 : ℝ) (5391490275567 / 5000000000000 : ℝ) (1347872568893 / 1250000000000 : ℝ) (289454682157 / 5000000000000 : ℝ) (578909364551 / 10000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog_289 (by norm_num [quadLogLo]) (by norm_num [quadLogHi])

private lemma hlog_291 : (11131078119873 / 10000000000000 : ℝ) ≤ Real.log (23209 / 7625 : ℝ) ∧ Real.log (23209 / 7625 : ℝ) ≤ (89048624959 / 80000000000 : ℝ) :=
  log_rat_bounds (23209 / 7625 : ℝ) (167 / 23042 : ℝ) (0) (1) (0) (11131078119873 / 10000000000000 : ℝ) (89048624959 / 80000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hqsub_292 :
    IntervalIntegrable (fun t => Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t)) volume (15187 / 7625 : ℝ) (15981 / 7625 : ℝ) ∧
      (113429766889 / 2000000000000 : ℝ) ≤ ∫ t in (15187 / 7625 : ℝ)..(15981 / 7625 : ℝ), Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (15187 / 7625 : ℝ)..(15981 / 7625 : ℝ), Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ≤ (56714883461 / 1000000000000 : ℝ) :=
  quad_log_div_sub (1 : ℝ) (1 : ℝ) (0 : ℝ) (1 : ℝ) (15187 / 7625 : ℝ) (15981 / 7625 : ℝ) (15584 / 7625 : ℝ) (397 / 7625 : ℝ)
    (23209 / 7625 : ℝ) (15584 / 7625 : ℝ) (7625 / 23209 : ℝ) (7625 / 15584 : ℝ) (7625 / 15584 : ℝ) (11131078119873 / 10000000000000 : ℝ) (89048624959 / 80000000000 : ℝ) (113429766889 / 2000000000000 : ℝ) (56714883461 / 1000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog_291 (by norm_num [quadLogLo]) (by norm_num [quadLogHi])

private lemma hlog_293 : (11467465000423 / 10000000000000 : ℝ) ≤ Real.log (24003 / 7625 : ℝ) ∧ Real.log (24003 / 7625 : ℝ) ≤ (11467465000429 / 10000000000000 : ℝ) :=
  log_rat_bounds (24003 / 7625 : ℝ) (1399 / 382649 : ℝ) (-3) (0) (2) (11467465000423 / 10000000000000 : ℝ) (11467465000429 / 10000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hqsub_294 :
    IntervalIntegrable (fun t => Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t)) volume (15981 / 7625 : ℝ) (11 / 5 : ℝ) ∧
      (555960889741 / 10000000000000 : ℝ) ≤ ∫ t in (15981 / 7625 : ℝ)..(11 / 5 : ℝ), Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (15981 / 7625 : ℝ)..(11 / 5 : ℝ), Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ≤ (277980444929 / 5000000000000 : ℝ) :=
  quad_log_div_sub (1 : ℝ) (1 : ℝ) (0 : ℝ) (1 : ℝ) (15981 / 7625 : ℝ) (11 / 5 : ℝ) (16378 / 7625 : ℝ) (397 / 7625 : ℝ)
    (24003 / 7625 : ℝ) (16378 / 7625 : ℝ) (7625 / 24003 : ℝ) (7625 / 16378 : ℝ) (7625 / 16378 : ℝ) (11467465000423 / 10000000000000 : ℝ) (11467465000429 / 10000000000000 : ℝ) (555960889741 / 10000000000000 : ℝ) (277980444929 / 5000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog_293 (by norm_num [quadLogLo]) (by norm_num [quadLogHi])

private lemma hqchain_295 :
    IntervalIntegrable (fun t => Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t)) volume (2561 / 1525 : ℝ) (14393 / 7625 : ℝ) ∧
      (239128890009 / 2000000000000 : ℝ) ≤ ∫ t in (2561 / 1525 : ℝ)..(14393 / 7625 : ℝ), Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (2561 / 1525 : ℝ)..(14393 / 7625 : ℝ), Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ≤ (298911112727 / 2500000000000 : ℝ) :=
  chain_int_bounds hqsub_286 hqsub_288 (by norm_num) (by norm_num)

private lemma hqchain_296 :
    IntervalIntegrable (fun t => Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t)) volume (2561 / 1525 : ℝ) (15187 / 7625 : ℝ) ∧
      (1774553814359 / 10000000000000 : ℝ) ≤ ∫ t in (2561 / 1525 : ℝ)..(15187 / 7625 : ℝ), Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (2561 / 1525 : ℝ)..(15187 / 7625 : ℝ), Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ≤ (1774553815459 / 10000000000000 : ℝ) :=
  chain_int_bounds hqchain_295 hqsub_290 (by norm_num) (by norm_num)

private lemma hqchain_297 :
    IntervalIntegrable (fun t => Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t)) volume (2561 / 1525 : ℝ) (15981 / 7625 : ℝ) ∧
      (585425662201 / 2500000000000 : ℝ) ≤ ∫ t in (2561 / 1525 : ℝ)..(15981 / 7625 : ℝ), Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (2561 / 1525 : ℝ)..(15981 / 7625 : ℝ), Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ≤ (2341702650069 / 10000000000000 : ℝ) :=
  chain_int_bounds hqchain_296 hqsub_292 (by norm_num) (by norm_num)

private lemma hqchain_298 :
    IntervalIntegrable (fun t => Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t)) volume (2561 / 1525 : ℝ) (11 / 5 : ℝ) ∧
      (579532707709 / 2000000000000 : ℝ) ≤ ∫ t in (2561 / 1525 : ℝ)..(11 / 5 : ℝ), Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (2561 / 1525 : ℝ)..(11 / 5 : ℝ), Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ≤ (2897663539927 / 10000000000000 : ℝ) :=
  chain_int_bounds hqchain_297 hqsub_294 (by norm_num) (by norm_num)

private lemma hlog_299 : (5925476268123 / 10000000000000 : ℝ) ≤ Real.log (27581 / 15250 : ℝ) ∧ Real.log (27581 / 15250 : ℝ) ≤ (5925476268127 / 10000000000000 : ℝ) :=
  log_rat_bounds (27581 / 15250 : ℝ) (131 / 55031 : ℝ) (0) (2) (-1) (5925476268123 / 10000000000000 : ℝ) (5925476268127 / 10000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hqsub_300 :
    IntervalIntegrable (fun t => Real.log ((177 / 50 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t)) volume (2561 / 1525 : ℝ) (13599 / 7625 : ℝ) ∧
      (178285196017 / 5000000000000 : ℝ) ≤ ∫ t in (2561 / 1525 : ℝ)..(13599 / 7625 : ℝ), Real.log ((177 / 50 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (2561 / 1525 : ℝ)..(13599 / 7625 : ℝ), Real.log ((177 / 50 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ≤ (178285196261 / 5000000000000 : ℝ) :=
  quad_log_div_sub (177 / 50 : ℝ) (-1 : ℝ) (0 : ℝ) (1 : ℝ) (2561 / 1525 : ℝ) (13599 / 7625 : ℝ) (13202 / 7625 : ℝ) (397 / 7625 : ℝ)
    (27581 / 15250 : ℝ) (13202 / 7625 : ℝ) (-15250 / 27581 : ℝ) (7625 / 13202 : ℝ) (7625 / 13202 : ℝ) (5925476268123 / 10000000000000 : ℝ) (5925476268127 / 10000000000000 : ℝ) (178285196017 / 5000000000000 : ℝ) (178285196261 / 5000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog_299 (by norm_num [quadLogLo]) (by norm_num [quadLogHi])

private lemma hlog_301 : (2666238839747 / 5000000000000 : ℝ) ≤ Real.log (25993 / 15250 : ℝ) ∧ Real.log (25993 / 15250 : ℝ) ≤ (10664955359 / 20000000000 : ℝ) :=
  log_rat_bounds (25993 / 15250 : ℝ) (2069 / 413819 : ℝ) (-4) (3) (0) (2666238839747 / 5000000000000 : ℝ) (10664955359 / 20000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hqsub_302 :
    IntervalIntegrable (fun t => Real.log ((177 / 50 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t)) volume (13599 / 7625 : ℝ) (14393 / 7625 : ℝ) ∧
      (302670934049 / 10000000000000 : ℝ) ≤ ∫ t in (13599 / 7625 : ℝ)..(14393 / 7625 : ℝ), Real.log ((177 / 50 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (13599 / 7625 : ℝ)..(14393 / 7625 : ℝ), Real.log ((177 / 50 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ≤ (37833866817 / 1250000000000 : ℝ) :=
  quad_log_div_sub (177 / 50 : ℝ) (-1 : ℝ) (0 : ℝ) (1 : ℝ) (13599 / 7625 : ℝ) (14393 / 7625 : ℝ) (13996 / 7625 : ℝ) (397 / 7625 : ℝ)
    (25993 / 15250 : ℝ) (13996 / 7625 : ℝ) (-15250 / 25993 : ℝ) (7625 / 13996 : ℝ) (15250 / 25993 : ℝ) (2666238839747 / 5000000000000 : ℝ) (10664955359 / 20000000000 : ℝ) (302670934049 / 10000000000000 : ℝ) (37833866817 / 1250000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog_301 (by norm_num [quadLogLo]) (by norm_num [quadLogHi])

private lemma hlog_303 : (940417052571 / 2000000000000 : ℝ) ≤ Real.log (4881 / 3050 : ℝ) ∧ Real.log (4881 / 3050 : ℝ) ≤ (4702085262859 / 10000000000000 : ℝ) :=
  log_rat_bounds (4881 / 3050 : ℝ) (1 / 9761 : ℝ) (3) (0) (-1) (940417052571 / 2000000000000 : ℝ) (4702085262859 / 10000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hqsub_304 :
    IntervalIntegrable (fun t => Real.log ((177 / 50 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t)) volume (14393 / 7625 : ℝ) (15187 / 7625 : ℝ) ∧
      (252553333757 / 10000000000000 : ℝ) ≤ ∫ t in (14393 / 7625 : ℝ)..(15187 / 7625 : ℝ), Real.log ((177 / 50 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (14393 / 7625 : ℝ)..(15187 / 7625 : ℝ), Real.log ((177 / 50 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ≤ (25255333441 / 1000000000000 : ℝ) :=
  quad_log_div_sub (177 / 50 : ℝ) (-1 : ℝ) (0 : ℝ) (1 : ℝ) (14393 / 7625 : ℝ) (15187 / 7625 : ℝ) (2958 / 1525 : ℝ) (397 / 7625 : ℝ)
    (4881 / 3050 : ℝ) (2958 / 1525 : ℝ) (-3050 / 4881 : ℝ) (1525 / 2958 : ℝ) (3050 / 4881 : ℝ) (940417052571 / 2000000000000 : ℝ) (4702085262859 / 10000000000000 : ℝ) (252553333757 / 10000000000000 : ℝ) (25255333441 / 1000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog_303 (by norm_num [quadLogLo]) (by norm_num [quadLogHi])

private lemma hlog_305 : (503657961387 / 1250000000000 : ℝ) ≤ Real.log (22817 / 15250 : ℝ) ∧ Real.log (22817 / 15250 : ℝ) ≤ (125914490347 / 312500000000 : ℝ) :=
  log_rat_bounds (22817 / 15250 : ℝ) (6059 / 1226059 : ℝ) (3) (-3) (1) (503657961387 / 1250000000000 : ℝ) (125914490347 / 312500000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hqsub_306 :
    IntervalIntegrable (fun t => Real.log ((177 / 50 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t)) volume (15187 / 7625 : ℝ) (15981 / 7625 : ℝ) ∧
      (102690956607 / 5000000000000 : ℝ) ≤ ∫ t in (15187 / 7625 : ℝ)..(15981 / 7625 : ℝ), Real.log ((177 / 50 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (15187 / 7625 : ℝ)..(15981 / 7625 : ℝ), Real.log ((177 / 50 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ≤ (205381914129 / 10000000000000 : ℝ) :=
  quad_log_div_sub (177 / 50 : ℝ) (-1 : ℝ) (0 : ℝ) (1 : ℝ) (15187 / 7625 : ℝ) (15981 / 7625 : ℝ) (15584 / 7625 : ℝ) (397 / 7625 : ℝ)
    (22817 / 15250 : ℝ) (15584 / 7625 : ℝ) (-15250 / 22817 : ℝ) (7625 / 15584 : ℝ) (15250 / 22817 : ℝ) (503657961387 / 1250000000000 : ℝ) (125914490347 / 312500000000 : ℝ) (102690956607 / 5000000000000 : ℝ) (205381914129 / 10000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog_305 (by norm_num [quadLogLo]) (by norm_num [quadLogHi])

private lemma hlog_307 : (3307886683961 / 10000000000000 : ℝ) ≤ Real.log (21229 / 15250 : ℝ) ∧ Real.log (21229 / 15250 : ℝ) ≤ (51685729437 / 156250000000 : ℝ) :=
  log_rat_bounds (21229 / 15250 : ℝ) (218 / 190843 : ℝ) (-1) (-2) (2) (3307886683961 / 10000000000000 : ℝ) (51685729437 / 156250000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hqsub_308 :
    IntervalIntegrable (fun t => Real.log ((177 / 50 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t)) volume (15981 / 7625 : ℝ) (11 / 5 : ℝ) ∧
      (160430150153 / 10000000000000 : ℝ) ≤ ∫ t in (15981 / 7625 : ℝ)..(11 / 5 : ℝ), Real.log ((177 / 50 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (15981 / 7625 : ℝ)..(11 / 5 : ℝ), Real.log ((177 / 50 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ≤ (160430151487 / 10000000000000 : ℝ) :=
  quad_log_div_sub (177 / 50 : ℝ) (-1 : ℝ) (0 : ℝ) (1 : ℝ) (15981 / 7625 : ℝ) (11 / 5 : ℝ) (16378 / 7625 : ℝ) (397 / 7625 : ℝ)
    (21229 / 15250 : ℝ) (16378 / 7625 : ℝ) (-15250 / 21229 : ℝ) (7625 / 16378 : ℝ) (15250 / 21229 : ℝ) (3307886683961 / 10000000000000 : ℝ) (51685729437 / 156250000000 : ℝ) (160430150153 / 10000000000000 : ℝ) (160430151487 / 10000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog_307 (by norm_num [quadLogLo]) (by norm_num [quadLogHi])

private lemma hqchain_309 :
    IntervalIntegrable (fun t => Real.log ((177 / 50 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t)) volume (2561 / 1525 : ℝ) (14393 / 7625 : ℝ) ∧
      (659241326083 / 10000000000000 : ℝ) ≤ ∫ t in (2561 / 1525 : ℝ)..(14393 / 7625 : ℝ), Real.log ((177 / 50 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (2561 / 1525 : ℝ)..(14393 / 7625 : ℝ), Real.log ((177 / 50 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ≤ (329620663529 / 5000000000000 : ℝ) :=
  chain_int_bounds hqsub_300 hqsub_302 (by norm_num) (by norm_num)

private lemma hqchain_310 :
    IntervalIntegrable (fun t => Real.log ((177 / 50 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t)) volume (2561 / 1525 : ℝ) (15187 / 7625 : ℝ) ∧
      (356169789 / 3906250000 : ℝ) ≤ ∫ t in (2561 / 1525 : ℝ)..(15187 / 7625 : ℝ), Real.log ((177 / 50 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (2561 / 1525 : ℝ)..(15187 / 7625 : ℝ), Real.log ((177 / 50 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ≤ (227948665367 / 2500000000000 : ℝ) :=
  chain_int_bounds hqchain_309 hqsub_304 (by norm_num) (by norm_num)

private lemma hqchain_311 :
    IntervalIntegrable (fun t => Real.log ((177 / 50 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t)) volume (2561 / 1525 : ℝ) (15981 / 7625 : ℝ) ∧
      (558588286527 / 5000000000000 : ℝ) ≤ ∫ t in (2561 / 1525 : ℝ)..(15981 / 7625 : ℝ), Real.log ((177 / 50 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (2561 / 1525 : ℝ)..(15981 / 7625 : ℝ), Real.log ((177 / 50 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ≤ (1117176575597 / 10000000000000 : ℝ) :=
  chain_int_bounds hqchain_310 hqsub_306 (by norm_num) (by norm_num)

private lemma hqchain_312 :
    IntervalIntegrable (fun t => Real.log ((177 / 50 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t)) volume (2561 / 1525 : ℝ) (11 / 5 : ℝ) ∧
      (1277606723207 / 10000000000000 : ℝ) ≤ ∫ t in (2561 / 1525 : ℝ)..(11 / 5 : ℝ), Real.log ((177 / 50 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (2561 / 1525 : ℝ)..(11 / 5 : ℝ), Real.log ((177 / 50 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ≤ (319401681771 / 2500000000000 : ℝ) :=
  chain_int_bounds hqchain_311 hqsub_308 (by norm_num) (by norm_num)

private lemma hact_tl_313 :
    IntervalIntegrable (fun t => Real.log ((t + 1) / ((36 / 25 : ℝ) * ((177 / 50 : ℝ) - t))) / ((5 : ℝ) * t)) volume (2561 / 1525 : ℝ) (11 / 5 : ℝ) ∧
      (127064726331 / 10000000000000 : ℝ) ≤ ∫ t in (2561 / 1525 : ℝ)..(11 / 5 : ℝ), Real.log ((t + 1) / ((36 / 25 : ℝ) * ((177 / 50 : ℝ) - t))) / ((5 : ℝ) * t) :=
  active_t_lin (5 : ℝ) (36 / 25 : ℝ) (177 / 50 : ℝ) (2561 / 1525 : ℝ) (11 / 5 : ℝ) (3355 / 2561 : ℝ) (29171449087 / 80000000000 : ℝ) (1823215567941 / 5000000000000 : ℝ) (1350269816029 / 5000000000000 : ℝ) (2700539632067 / 10000000000000 : ℝ)
    (579532707709 / 2000000000000 : ℝ) (2897663539927 / 10000000000000 : ℝ) (1277606723207 / 10000000000000 : ℝ) (319401681771 / 2500000000000 : ℝ) (127064726331 / 10000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog_283 hlog_284 hqchain_298 hqchain_312 (by norm_num)

private lemma hterm_282 :
    IntervalIntegrable (fun t => ind (2561 / 1525 : ℝ) (127 / 50 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) / ((36 / 25 : ℝ) * ((177 / 50 : ℝ) - t)))) volume (1 : ℝ) (11 / 5 : ℝ) ∧
      (127064726331 / 10000000000000 : ℝ) ≤ ∫ t in (1 : ℝ)..(11 / 5 : ℝ), ind (2561 / 1525 : ℝ) (127 / 50 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) / ((36 / 25 : ℝ) * ((177 / 50 : ℝ) - t))) :=
  bound_ind_div_active (1 : ℝ) (11 / 5 : ℝ) (2561 / 1525 : ℝ) (127 / 50 : ℝ) (2561 / 1525 : ℝ) (11 / 5 : ℝ) (127064726331 / 10000000000000 : ℝ)
    (fun t => (5 : ℝ) * t) (fun t => (t + 1) / ((36 / 25 : ℝ) * ((177 / 50 : ℝ) - t)))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (Or.inr rfl) (Or.inl rfl) hact_tl_313

private lemma hlog_315 : (3988752984287 / 10000000000000 : ℝ) ≤ Real.log (605 / 406 : ℝ) ∧ Real.log (605 / 406 : ℝ) ≤ (1994376492147 / 5000000000000 : ℝ) :=
  log_rat_bounds (605 / 406 : ℝ) (19 / 6515 : ℝ) (3) (-3) (1) (3988752984287 / 10000000000000 : ℝ) (1994376492147 / 5000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hlog_316 : (186170176641 / 200000000000 : ℝ) ≤ Real.log (761 / 300 : ℝ) ∧ Real.log (761 / 300 : ℝ) ≤ (4654254416029 / 5000000000000 : ℝ) :=
  log_rat_bounds (761 / 300 : ℝ) (13 / 12163 : ℝ) (-5) (4) (0) (186170176641 / 200000000000 : ℝ) (4654254416029 / 5000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hqsub_317 :
    IntervalIntegrable (fun t => Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t)) volume (406 / 275 : ℝ) (527 / 330 : ℝ) ∧
      (730640077777 / 10000000000000 : ℝ) ≤ ∫ t in (406 / 275 : ℝ)..(527 / 330 : ℝ), Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (406 / 275 : ℝ)..(527 / 330 : ℝ), Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ≤ (730640081069 / 10000000000000 : ℝ) :=
  quad_log_div_sub (1 : ℝ) (1 : ℝ) (0 : ℝ) (1 : ℝ) (406 / 275 : ℝ) (527 / 330 : ℝ) (461 / 300 : ℝ) (199 / 3300 : ℝ)
    (761 / 300 : ℝ) (461 / 300 : ℝ) (300 / 761 : ℝ) (300 / 461 : ℝ) (300 / 461 : ℝ) (186170176641 / 200000000000 : ℝ) (4654254416029 / 5000000000000 : ℝ) (730640077777 / 10000000000000 : ℝ) (730640081069 / 10000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog_316 (by norm_num [quadLogLo]) (by norm_num [quadLogHi])

private lemma hlog_318 : (9773003063243 / 10000000000000 : ℝ) ≤ Real.log (2923 / 1100 : ℝ) ∧ Real.log (2923 / 1100 : ℝ) ≤ (2443250765813 / 2500000000000 : ℝ) :=
  log_rat_bounds (2923 / 1100 : ℝ) (701 / 69451 : ℝ) (-4) (-1) (3) (9773003063243 / 10000000000000 : ℝ) (2443250765813 / 2500000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hqsub_319 :
    IntervalIntegrable (fun t => Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t)) volume (527 / 330 : ℝ) (1417 / 825 : ℝ) ∧
      (177817462289 / 2500000000000 : ℝ) ≤ ∫ t in (527 / 330 : ℝ)..(1417 / 825 : ℝ), Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (527 / 330 : ℝ)..(1417 / 825 : ℝ), Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ≤ (177817462777 / 2500000000000 : ℝ) :=
  quad_log_div_sub (1 : ℝ) (1 : ℝ) (0 : ℝ) (1 : ℝ) (527 / 330 : ℝ) (1417 / 825 : ℝ) (1823 / 1100 : ℝ) (199 / 3300 : ℝ)
    (2923 / 1100 : ℝ) (1823 / 1100 : ℝ) (1100 / 2923 : ℝ) (1100 / 1823 : ℝ) (1100 / 1823 : ℝ) (9773003063243 / 10000000000000 : ℝ) (2443250765813 / 2500000000000 : ℝ) (177817462289 / 2500000000000 : ℝ) (177817462777 / 2500000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog_318 (by norm_num [quadLogLo]) (by norm_num [quadLogHi])

private lemma hlog_320 : (10216876105069 / 10000000000000 : ℝ) ≤ Real.log (9167 / 3300 : ℝ) ∧ Real.log (9167 / 3300 : ℝ) ≤ (5108438052537 / 5000000000000 : ℝ) :=
  log_rat_bounds (9167 / 3300 : ℝ) (1 / 55001 : ℝ) (0) (-2) (2) (10216876105069 / 10000000000000 : ℝ) (5108438052537 / 5000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hqsub_321 :
    IntervalIntegrable (fun t => Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t)) volume (1417 / 825 : ℝ) (1011 / 550 : ℝ) ∧
      (346564401321 / 5000000000000 : ℝ) ≤ ∫ t in (1417 / 825 : ℝ)..(1011 / 550 : ℝ), Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (1417 / 825 : ℝ)..(1011 / 550 : ℝ), Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ≤ (173282200961 / 2500000000000 : ℝ) :=
  quad_log_div_sub (1 : ℝ) (1 : ℝ) (0 : ℝ) (1 : ℝ) (1417 / 825 : ℝ) (1011 / 550 : ℝ) (5867 / 3300 : ℝ) (199 / 3300 : ℝ)
    (9167 / 3300 : ℝ) (5867 / 3300 : ℝ) (3300 / 9167 : ℝ) (3300 / 5867 : ℝ) (3300 / 5867 : ℝ) (10216876105069 / 10000000000000 : ℝ) (5108438052537 / 5000000000000 : ℝ) (346564401321 / 5000000000000 : ℝ) (173282200961 / 2500000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog_320 (by norm_num [quadLogLo]) (by norm_num [quadLogHi])

private lemma hlog_322 : (5320940672097 / 5000000000000 : ℝ) ≤ Real.log (1913 / 660 : ℝ) ∧ Real.log (1913 / 660 : ℝ) ≤ (10641881344201 / 10000000000000 : ℝ) :=
  log_rat_bounds (1913 / 660 : ℝ) (61 / 19069 : ℝ) (3) (2) (-2) (5320940672097 / 5000000000000 : ℝ) (10641881344201 / 10000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hqsub_323 :
    IntervalIntegrable (fun t => Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t)) volume (1011 / 550 : ℝ) (1616 / 825 : ℝ) ∧
      (676094080237 / 10000000000000 : ℝ) ≤ ∫ t in (1011 / 550 : ℝ)..(1616 / 825 : ℝ), Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (1011 / 550 : ℝ)..(1616 / 825 : ℝ), Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ≤ (338047040501 / 5000000000000 : ℝ) :=
  quad_log_div_sub (1 : ℝ) (1 : ℝ) (0 : ℝ) (1 : ℝ) (1011 / 550 : ℝ) (1616 / 825 : ℝ) (1253 / 660 : ℝ) (199 / 3300 : ℝ)
    (1913 / 660 : ℝ) (1253 / 660 : ℝ) (660 / 1913 : ℝ) (660 / 1253 : ℝ) (660 / 1253 : ℝ) (5320940672097 / 5000000000000 : ℝ) (10641881344201 / 10000000000000 : ℝ) (676094080237 / 10000000000000 : ℝ) (338047040501 / 5000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog_322 (by norm_num [quadLogLo]) (by norm_num [quadLogHi])

private lemma hlog_324 : (11049557625901 / 10000000000000 : ℝ) ≤ Real.log (3321 / 1100 : ℝ) ∧ Real.log (3321 / 1100 : ℝ) ≤ (11049557625903 / 10000000000000 : ℝ) :=
  log_rat_bounds (3321 / 1100 : ℝ) (7 / 2207 : ℝ) (0) (1) (0) (11049557625901 / 10000000000000 : ℝ) (11049557625903 / 10000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hqsub_325 :
    IntervalIntegrable (fun t => Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t)) volume (1616 / 825 : ℝ) (3431 / 1650 : ℝ) ∧
      (132011871687 / 2000000000000 : ℝ) ≤ ∫ t in (1616 / 825 : ℝ)..(3431 / 1650 : ℝ), Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (1616 / 825 : ℝ)..(3431 / 1650 : ℝ), Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ≤ (330029679467 / 5000000000000 : ℝ) :=
  quad_log_div_sub (1 : ℝ) (1 : ℝ) (0 : ℝ) (1 : ℝ) (1616 / 825 : ℝ) (3431 / 1650 : ℝ) (2221 / 1100 : ℝ) (199 / 3300 : ℝ)
    (3321 / 1100 : ℝ) (2221 / 1100 : ℝ) (1100 / 3321 : ℝ) (1100 / 2221 : ℝ) (1100 / 2221 : ℝ) (11049557625901 / 10000000000000 : ℝ) (11049557625903 / 10000000000000 : ℝ) (132011871687 / 2000000000000 : ℝ) (330029679467 / 5000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog_324 (by norm_num [quadLogLo]) (by norm_num [quadLogHi])

private lemma hlog_326 : (357539465249 / 312500000000 : ℝ) ≤ Real.log (10361 / 3300 : ℝ) ∧ Real.log (10361 / 3300 : ℝ) ≤ (5720631443987 / 5000000000000 : ℝ) :=
  log_rat_bounds (10361 / 3300 : ℝ) (97 / 41347 : ℝ) (-3) (0) (2) (357539465249 / 312500000000 : ℝ) (5720631443987 / 5000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hqsub_327 :
    IntervalIntegrable (fun t => Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t)) volume (3431 / 1650 : ℝ) (11 / 5 : ℝ) ∧
      (128986417109 / 2000000000000 : ℝ) ≤ ∫ t in (3431 / 1650 : ℝ)..(11 / 5 : ℝ), Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (3431 / 1650 : ℝ)..(11 / 5 : ℝ), Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ≤ (16123302147 / 250000000000 : ℝ) :=
  quad_log_div_sub (1 : ℝ) (1 : ℝ) (0 : ℝ) (1 : ℝ) (3431 / 1650 : ℝ) (11 / 5 : ℝ) (7061 / 3300 : ℝ) (199 / 3300 : ℝ)
    (10361 / 3300 : ℝ) (7061 / 3300 : ℝ) (3300 / 10361 : ℝ) (3300 / 7061 : ℝ) (3300 / 7061 : ℝ) (357539465249 / 312500000000 : ℝ) (5720631443987 / 5000000000000 : ℝ) (128986417109 / 2000000000000 : ℝ) (16123302147 / 250000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog_326 (by norm_num [quadLogLo]) (by norm_num [quadLogHi])

private lemma hqchain_328 :
    IntervalIntegrable (fun t => Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t)) volume (406 / 275 : ℝ) (1417 / 825 : ℝ) ∧
      (1441909926933 / 10000000000000 : ℝ) ≤ ∫ t in (406 / 275 : ℝ)..(1417 / 825 : ℝ), Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (406 / 275 : ℝ)..(1417 / 825 : ℝ), Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ≤ (1441909932177 / 10000000000000 : ℝ) :=
  chain_int_bounds hqsub_317 hqsub_319 (by norm_num) (by norm_num)

private lemma hqchain_329 :
    IntervalIntegrable (fun t => Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t)) volume (406 / 275 : ℝ) (1011 / 550 : ℝ) ∧
      (85401549183 / 400000000000 : ℝ) ≤ ∫ t in (406 / 275 : ℝ)..(1011 / 550 : ℝ), Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (406 / 275 : ℝ)..(1011 / 550 : ℝ), Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ≤ (2135038736021 / 10000000000000 : ℝ) :=
  chain_int_bounds hqchain_328 hqsub_321 (by norm_num) (by norm_num)

private lemma hqchain_330 :
    IntervalIntegrable (fun t => Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t)) volume (406 / 275 : ℝ) (1616 / 825 : ℝ) ∧
      (702783202453 / 2500000000000 : ℝ) ≤ ∫ t in (406 / 275 : ℝ)..(1616 / 825 : ℝ), Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (406 / 275 : ℝ)..(1616 / 825 : ℝ), Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ≤ (2811132817023 / 10000000000000 : ℝ) :=
  chain_int_bounds hqchain_329 hqsub_323 (by norm_num) (by norm_num)

private lemma hqchain_331 :
    IntervalIntegrable (fun t => Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t)) volume (406 / 275 : ℝ) (3431 / 1650 : ℝ) ∧
      (3471192168247 / 10000000000000 : ℝ) ≤ ∫ t in (406 / 275 : ℝ)..(3431 / 1650 : ℝ), Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (406 / 275 : ℝ)..(3431 / 1650 : ℝ), Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ≤ (3471192175957 / 10000000000000 : ℝ) :=
  chain_int_bounds hqchain_330 hqsub_325 (by norm_num) (by norm_num)

private lemma hqchain_332 :
    IntervalIntegrable (fun t => Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t)) volume (406 / 275 : ℝ) (11 / 5 : ℝ) ∧
      (128628882931 / 312500000000 : ℝ) ≤ ∫ t in (406 / 275 : ℝ)..(11 / 5 : ℝ), Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (406 / 275 : ℝ)..(11 / 5 : ℝ), Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ≤ (4116124261837 / 10000000000000 : ℝ) :=
  chain_int_bounds hqchain_331 hqsub_327 (by norm_num) (by norm_num)

private lemma hlog_333 : (6948124598789 / 10000000000000 : ℝ) ≤ Real.log (601 / 300 : ℝ) ∧ Real.log (601 / 300 : ℝ) ≤ (6948124598791 / 10000000000000 : ℝ) :=
  log_rat_bounds (601 / 300 : ℝ) (1 / 1201 : ℝ) (1) (0) (0) (6948124598789 / 10000000000000 : ℝ) (6948124598791 / 10000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hqsub_334 :
    IntervalIntegrable (fun t => Real.log ((177 / 50 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t)) volume (406 / 275 : ℝ) (527 / 330 : ℝ) ∧
      (68224747283 / 1250000000000 : ℝ) ≤ ∫ t in (406 / 275 : ℝ)..(527 / 330 : ℝ), Real.log ((177 / 50 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (406 / 275 : ℝ)..(527 / 330 : ℝ), Real.log ((177 / 50 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ≤ (68224747681 / 1250000000000 : ℝ) :=
  quad_log_div_sub (177 / 50 : ℝ) (-1 : ℝ) (0 : ℝ) (1 : ℝ) (406 / 275 : ℝ) (527 / 330 : ℝ) (461 / 300 : ℝ) (199 / 3300 : ℝ)
    (601 / 300 : ℝ) (461 / 300 : ℝ) (-300 / 601 : ℝ) (300 / 461 : ℝ) (300 / 461 : ℝ) (6948124598789 / 10000000000000 : ℝ) (6948124598791 / 10000000000000 : ℝ) (68224747283 / 1250000000000 : ℝ) (68224747681 / 1250000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog_333 (by norm_num [quadLogLo]) (by norm_num [quadLogHi])

private lemma hlog_335 : (790901753261 / 1250000000000 : ℝ) ≤ Real.log (2071 / 1100 : ℝ) ∧ Real.log (2071 / 1100 : ℝ) ≤ (3163607013047 / 5000000000000 : ℝ) :=
  log_rat_bounds (2071 / 1100 : ℝ) (17 / 8267 : ℝ) (-3) (1) (1) (790901753261 / 1250000000000 : ℝ) (3163607013047 / 5000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hqsub_336 :
    IntervalIntegrable (fun t => Real.log ((177 / 50 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t)) volume (527 / 330 : ℝ) (1417 / 825 : ℝ) ∧
      (460817316771 / 10000000000000 : ℝ) ≤ ∫ t in (527 / 330 : ℝ)..(1417 / 825 : ℝ), Real.log ((177 / 50 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (527 / 330 : ℝ)..(1417 / 825 : ℝ), Real.log ((177 / 50 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ≤ (460817318631 / 10000000000000 : ℝ) :=
  quad_log_div_sub (177 / 50 : ℝ) (-1 : ℝ) (0 : ℝ) (1 : ℝ) (527 / 330 : ℝ) (1417 / 825 : ℝ) (1823 / 1100 : ℝ) (199 / 3300 : ℝ)
    (2071 / 1100 : ℝ) (1823 / 1100 : ℝ) (-1100 / 2071 : ℝ) (1100 / 1823 : ℝ) (1100 / 1823 : ℝ) (790901753261 / 1250000000000 : ℝ) (3163607013047 / 5000000000000 : ℝ) (460817316771 / 10000000000000 : ℝ) (460817318631 / 10000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog_335 (by norm_num [quadLogLo]) (by norm_num [quadLogHi])

private lemma hlog_337 : (5665183174977 / 10000000000000 : ℝ) ≤ Real.log (1163 / 660 : ℝ) ∧ Real.log (1163 / 660 : ℝ) ≤ (5665183174987 / 10000000000000 : ℝ) :=
  log_rat_bounds (1163 / 660 : ℝ) (91 / 74341 : ℝ) (-7) (2) (2) (5665183174977 / 10000000000000 : ℝ) (5665183174987 / 10000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hqsub_338 :
    IntervalIntegrable (fun t => Real.log ((177 / 50 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t)) volume (1417 / 825 : ℝ) (1011 / 550 : ℝ) ∧
      (384586988627 / 10000000000000 : ℝ) ≤ ∫ t in (1417 / 825 : ℝ)..(1011 / 550 : ℝ), Real.log ((177 / 50 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (1417 / 825 : ℝ)..(1011 / 550 : ℝ), Real.log ((177 / 50 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ≤ (384586989811 / 10000000000000 : ℝ) :=
  quad_log_div_sub (177 / 50 : ℝ) (-1 : ℝ) (0 : ℝ) (1 : ℝ) (1417 / 825 : ℝ) (1011 / 550 : ℝ) (5867 / 3300 : ℝ) (199 / 3300 : ℝ)
    (1163 / 660 : ℝ) (5867 / 3300 : ℝ) (-660 / 1163 : ℝ) (3300 / 5867 : ℝ) (660 / 1163 : ℝ) (5665183174977 / 10000000000000 : ℝ) (5665183174987 / 10000000000000 : ℝ) (384586988627 / 10000000000000 : ℝ) (384586989811 / 10000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog_337 (by norm_num [quadLogLo]) (by norm_num [quadLogHi])

private lemma hlog_339 : (4956196882029 / 10000000000000 : ℝ) ≤ Real.log (5417 / 3300 : ℝ) ∧ Real.log (5417 / 3300 : ℝ) ≤ (4956196882037 / 10000000000000 : ℝ) :=
  log_rat_bounds (5417 / 3300 : ℝ) (71 / 10763 : ℝ) (-1) (4) (-2) (4956196882029 / 10000000000000 : ℝ) (4956196882037 / 10000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hqsub_340 :
    IntervalIntegrable (fun t => Real.log ((177 / 50 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t)) volume (1011 / 550 : ℝ) (1616 / 825 : ℝ) ∧
      (157532598977 / 5000000000000 : ℝ) ≤ ∫ t in (1011 / 550 : ℝ)..(1616 / 825 : ℝ), Real.log ((177 / 50 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (1011 / 550 : ℝ)..(1616 / 825 : ℝ), Real.log ((177 / 50 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ≤ (19691574973 / 625000000000 : ℝ) :=
  quad_log_div_sub (177 / 50 : ℝ) (-1 : ℝ) (0 : ℝ) (1 : ℝ) (1011 / 550 : ℝ) (1616 / 825 : ℝ) (1253 / 660 : ℝ) (199 / 3300 : ℝ)
    (5417 / 3300 : ℝ) (1253 / 660 : ℝ) (-3300 / 5417 : ℝ) (660 / 1253 : ℝ) (3300 / 5417 : ℝ) (4956196882029 / 10000000000000 : ℝ) (4956196882037 / 10000000000000 : ℝ) (157532598977 / 5000000000000 : ℝ) (19691574973 / 625000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog_339 (by norm_num [quadLogLo]) (by norm_num [quadLogHi])

private lemma hlog_341 : (2096541211001 / 5000000000000 : ℝ) ≤ Real.log (1673 / 1100 : ℝ) ∧ Real.log (1673 / 1100 : ℝ) ≤ (838616484401 / 2000000000000 : ℝ) :=
  log_rat_bounds (1673 / 1100 : ℝ) (23 / 3323 : ℝ) (-1) (1) (0) (2096541211001 / 5000000000000 : ℝ) (838616484401 / 2000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hqsub_342 :
    IntervalIntegrable (fun t => Real.log ((177 / 50 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t)) volume (1616 / 825 : ℝ) (3431 / 1650 : ℝ) ∧
      (250618604751 / 10000000000000 : ℝ) ≤ ∫ t in (1616 / 825 : ℝ)..(3431 / 1650 : ℝ), Real.log ((177 / 50 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (1616 / 825 : ℝ)..(3431 / 1650 : ℝ), Real.log ((177 / 50 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ≤ (250618607101 / 10000000000000 : ℝ) :=
  quad_log_div_sub (177 / 50 : ℝ) (-1 : ℝ) (0 : ℝ) (1 : ℝ) (1616 / 825 : ℝ) (3431 / 1650 : ℝ) (2221 / 1100 : ℝ) (199 / 3300 : ℝ)
    (1673 / 1100 : ℝ) (2221 / 1100 : ℝ) (-1100 / 1673 : ℝ) (1100 / 2221 : ℝ) (1100 / 1673 : ℝ) (2096541211001 / 5000000000000 : ℝ) (838616484401 / 2000000000000 : ℝ) (250618604751 / 10000000000000 : ℝ) (250618607101 / 10000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog_341 (by norm_num [quadLogLo]) (by norm_num [quadLogHi])

private lemma hlog_343 : (1683443317077 / 5000000000000 : ℝ) ≤ Real.log (4621 / 3300 : ℝ) ∧ Real.log (4621 / 3300 : ℝ) ≤ (42086082927 / 125000000000 : ℝ) :=
  log_rat_bounds (4621 / 3300 : ℝ) (113 / 27613 : ℝ) (-1) (-2) (2) (1683443317077 / 5000000000000 : ℝ) (42086082927 / 125000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hqsub_344 :
    IntervalIntegrable (fun t => Real.log ((177 / 50 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t)) volume (3431 / 1650 : ℝ) (11 / 5 : ℝ) ∧
      (189881870851 / 10000000000000 : ℝ) ≤ ∫ t in (3431 / 1650 : ℝ)..(11 / 5 : ℝ), Real.log ((177 / 50 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (3431 / 1650 : ℝ)..(11 / 5 : ℝ), Real.log ((177 / 50 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ≤ (94940937231 / 5000000000000 : ℝ) :=
  quad_log_div_sub (177 / 50 : ℝ) (-1 : ℝ) (0 : ℝ) (1 : ℝ) (3431 / 1650 : ℝ) (11 / 5 : ℝ) (7061 / 3300 : ℝ) (199 / 3300 : ℝ)
    (4621 / 3300 : ℝ) (7061 / 3300 : ℝ) (-3300 / 4621 : ℝ) (3300 / 7061 : ℝ) (3300 / 4621 : ℝ) (1683443317077 / 5000000000000 : ℝ) (42086082927 / 125000000000 : ℝ) (189881870851 / 10000000000000 : ℝ) (94940937231 / 5000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog_343 (by norm_num [quadLogLo]) (by norm_num [quadLogHi])

private lemma hqchain_345 :
    IntervalIntegrable (fun t => Real.log ((177 / 50 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t)) volume (406 / 275 : ℝ) (1417 / 825 : ℝ) ∧
      (201323059007 / 2000000000000 : ℝ) ≤ ∫ t in (406 / 275 : ℝ)..(1417 / 825 : ℝ), Real.log ((177 / 50 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (406 / 275 : ℝ)..(1417 / 825 : ℝ), Real.log ((177 / 50 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ≤ (1006615300079 / 10000000000000 : ℝ) :=
  chain_int_bounds hqsub_334 hqsub_336 (by norm_num) (by norm_num)

private lemma hqchain_346 :
    IntervalIntegrable (fun t => Real.log ((177 / 50 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t)) volume (406 / 275 : ℝ) (1011 / 550 : ℝ) ∧
      (695601141831 / 5000000000000 : ℝ) ≤ ∫ t in (406 / 275 : ℝ)..(1011 / 550 : ℝ), Real.log ((177 / 50 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (406 / 275 : ℝ)..(1011 / 550 : ℝ), Real.log ((177 / 50 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ≤ (139120228989 / 1000000000000 : ℝ) :=
  chain_int_bounds hqchain_345 hqsub_338 (by norm_num) (by norm_num)

private lemma hqchain_347 :
    IntervalIntegrable (fun t => Real.log ((177 / 50 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t)) volume (406 / 275 : ℝ) (1616 / 825 : ℝ) ∧
      (106641717601 / 625000000000 : ℝ) ≤ ∫ t in (406 / 275 : ℝ)..(1616 / 825 : ℝ), Real.log ((177 / 50 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (406 / 275 : ℝ)..(1616 / 825 : ℝ), Real.log ((177 / 50 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ≤ (853133744729 / 5000000000000 : ℝ) :=
  chain_int_bounds hqchain_346 hqsub_340 (by norm_num) (by norm_num)

private lemma hqchain_348 :
    IntervalIntegrable (fun t => Real.log ((177 / 50 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t)) volume (406 / 275 : ℝ) (3431 / 1650 : ℝ) ∧
      (1956886086367 / 10000000000000 : ℝ) ≤ ∫ t in (406 / 275 : ℝ)..(3431 / 1650 : ℝ), Real.log ((177 / 50 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (406 / 275 : ℝ)..(3431 / 1650 : ℝ), Real.log ((177 / 50 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ≤ (1956886096559 / 10000000000000 : ℝ) :=
  chain_int_bounds hqchain_347 hqsub_342 (by norm_num) (by norm_num)

private lemma hqchain_349 :
    IntervalIntegrable (fun t => Real.log ((177 / 50 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t)) volume (406 / 275 : ℝ) (11 / 5 : ℝ) ∧
      (1073383978609 / 5000000000000 : ℝ) ≤ ∫ t in (406 / 275 : ℝ)..(11 / 5 : ℝ), Real.log ((177 / 50 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (406 / 275 : ℝ)..(11 / 5 : ℝ), Real.log ((177 / 50 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ≤ (2146767971021 / 10000000000000 : ℝ) :=
  chain_int_bounds hqchain_348 hqsub_344 (by norm_num) (by norm_num)

private lemma hact_tl_350 :
    IntervalIntegrable (fun t => Real.log ((t + 1) / ((6 / 5 : ℝ) * ((177 / 50 : ℝ) - t))) / ((5 : ℝ) * t)) volume (406 / 275 : ℝ) (11 / 5 : ℝ) ∧
      (248424125801 / 10000000000000 : ℝ) ≤ ∫ t in (406 / 275 : ℝ)..(11 / 5 : ℝ), Real.log ((t + 1) / ((6 / 5 : ℝ) * ((177 / 50 : ℝ) - t))) / ((5 : ℝ) * t) :=
  active_t_lin (5 : ℝ) (6 / 5 : ℝ) (177 / 50 : ℝ) (406 / 275 : ℝ) (11 / 5 : ℝ) (605 / 406 : ℝ) (1823215567937 / 10000000000000 : ℝ) (1823215567941 / 10000000000000 : ℝ) (3988752984287 / 10000000000000 : ℝ) (1994376492147 / 5000000000000 : ℝ)
    (128628882931 / 312500000000 : ℝ) (4116124261837 / 10000000000000 : ℝ) (1073383978609 / 5000000000000 : ℝ) (2146767971021 / 10000000000000 : ℝ) (248424125801 / 10000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog_161 hlog_315 hqchain_332 hqchain_349 (by norm_num)

private lemma hterm_314 :
    IntervalIntegrable (fun t => ind (406 / 275 : ℝ) (127 / 50 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) / ((6 / 5 : ℝ) * ((177 / 50 : ℝ) - t)))) volume (1 : ℝ) (11 / 5 : ℝ) ∧
      (248424125801 / 10000000000000 : ℝ) ≤ ∫ t in (1 : ℝ)..(11 / 5 : ℝ), ind (406 / 275 : ℝ) (127 / 50 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) / ((6 / 5 : ℝ) * ((177 / 50 : ℝ) - t))) :=
  bound_ind_div_active (1 : ℝ) (11 / 5 : ℝ) (406 / 275 : ℝ) (127 / 50 : ℝ) (406 / 275 : ℝ) (11 / 5 : ℝ) (248424125801 / 10000000000000 : ℝ)
    (fun t => (5 : ℝ) * t) (fun t => (t + 1) / ((6 / 5 : ℝ) * ((177 / 50 : ℝ) - t)))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (Or.inr rfl) (Or.inl rfl) hact_tl_350

private lemma hlog_352 : (3140146377823 / 2000000000000 : ℝ) ≤ Real.log (4807 / 1000 : ℝ) ∧ Real.log (4807 / 1000 : ℝ) ≤ (98129574307 / 62500000000 : ℝ) :=
  log_rat_bounds (4807 / 1000 : ℝ) (7 / 9607 : ℝ) (3) (1) (-1) (3140146377823 / 2000000000000 : ℝ) (98129574307 / 62500000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hlog_353 : (726379249919 / 2000000000000 : ℝ) ≤ Real.log (220 / 153 : ℝ) ∧ Real.log (220 / 153 : ℝ) ≤ (3631896249603 / 10000000000000 : ℝ) :=
  log_rat_bounds (220 / 153 : ℝ) (3 / 547 : ℝ) (6) (-2) (-1) (726379249919 / 2000000000000 : ℝ) (3631896249603 / 10000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hlog_354 : (9500478286719 / 10000000000000 : ℝ) ≤ Real.log (3103 / 1200 : ℝ) ∧ Real.log (3103 / 1200 : ℝ) ≤ (4750239143363 / 5000000000000 : ℝ) :=
  log_rat_bounds (3103 / 1200 : ℝ) (31 / 6175 : ℝ) (6) (0) (-2) (9500478286719 / 10000000000000 : ℝ) (4750239143363 / 5000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hqsub_355 :
    IntervalIntegrable (fun t => Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t)) volume (153 / 100 : ℝ) (197 / 120 : ℝ) ∧
      (167255181879 / 2500000000000 : ℝ) ≤ ∫ t in (153 / 100 : ℝ)..(197 / 120 : ℝ), Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (153 / 100 : ℝ)..(197 / 120 : ℝ), Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ≤ (669020729061 / 10000000000000 : ℝ) :=
  quad_log_div_sub (1 : ℝ) (1 : ℝ) (0 : ℝ) (1 : ℝ) (153 / 100 : ℝ) (197 / 120 : ℝ) (1903 / 1200 : ℝ) (67 / 1200 : ℝ)
    (3103 / 1200 : ℝ) (1903 / 1200 : ℝ) (1200 / 3103 : ℝ) (1200 / 1903 : ℝ) (1200 / 1903 : ℝ) (9500478286719 / 10000000000000 : ℝ) (4750239143363 / 5000000000000 : ℝ) (167255181879 / 2500000000000 : ℝ) (669020729061 / 10000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog_354 (by norm_num [quadLogLo]) (by norm_num [quadLogHi])

private lemma hlog_356 : (9923254181499 / 10000000000000 : ℝ) ≤ Real.log (1079 / 400 : ℝ) ∧ Real.log (1079 / 400 : ℝ) ≤ (9923254181503 / 10000000000000 : ℝ) :=
  log_rat_bounds (1079 / 400 : ℝ) (37 / 6437 : ℝ) (3) (-1) (0) (9923254181499 / 10000000000000 : ℝ) (9923254181503 / 10000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hqsub_357 :
    IntervalIntegrable (fun t => Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t)) volume (197 / 120 : ℝ) (263 / 150 : ℝ) ∧
      (81602591057 / 1250000000000 : ℝ) ≤ ∫ t in (197 / 120 : ℝ)..(263 / 150 : ℝ), Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (197 / 120 : ℝ)..(263 / 150 : ℝ), Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ≤ (652820729421 / 10000000000000 : ℝ) :=
  quad_log_div_sub (1 : ℝ) (1 : ℝ) (0 : ℝ) (1 : ℝ) (197 / 120 : ℝ) (263 / 150 : ℝ) (679 / 400 : ℝ) (67 / 1200 : ℝ)
    (1079 / 400 : ℝ) (679 / 400 : ℝ) (400 / 1079 : ℝ) (400 / 679 : ℝ) (400 / 679 : ℝ) (9923254181499 / 10000000000000 : ℝ) (9923254181503 / 10000000000000 : ℝ) (81602591057 / 1250000000000 : ℝ) (652820729421 / 10000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog_356 (by norm_num [quadLogLo]) (by norm_num [quadLogHi])

private lemma hlog_358 : (645554924661 / 625000000000 : ℝ) ≤ Real.log (3371 / 1200 : ℝ) ∧ Real.log (3371 / 1200 : ℝ) ≤ (5164439397291 / 5000000000000 : ℝ) :=
  log_rat_bounds (3371 / 1200 : ℝ) (113 / 20113 : ℝ) (0) (-2) (2) (645554924661 / 625000000000 : ℝ) (5164439397291 / 5000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hqsub_359 :
    IntervalIntegrable (fun t => Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t)) volume (263 / 150 : ℝ) (373 / 200 : ℝ) ∧
      (318780970877 / 5000000000000 : ℝ) ≤ ∫ t in (263 / 150 : ℝ)..(373 / 200 : ℝ), Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (263 / 150 : ℝ)..(373 / 200 : ℝ), Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ≤ (79695242797 / 1250000000000 : ℝ) :=
  quad_log_div_sub (1 : ℝ) (1 : ℝ) (0 : ℝ) (1 : ℝ) (263 / 150 : ℝ) (373 / 200 : ℝ) (2171 / 1200 : ℝ) (67 / 1200 : ℝ)
    (3371 / 1200 : ℝ) (2171 / 1200 : ℝ) (1200 / 3371 : ℝ) (1200 / 2171 : ℝ) (1200 / 2171 : ℝ) (645554924661 / 625000000000 : ℝ) (5164439397291 / 5000000000000 : ℝ) (318780970877 / 5000000000000 : ℝ) (79695242797 / 1250000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog_358 (by norm_num [quadLogLo]) (by norm_num [quadLogHi])

private lemma hlog_360 : (5359344818461 / 5000000000000 : ℝ) ≤ Real.log (701 / 240 : ℝ) ∧ Real.log (701 / 240 : ℝ) ≤ (10718689636929 / 10000000000000 : ℝ) :=
  log_rat_bounds (701 / 240 : ℝ) (49 / 6961 : ℝ) (3) (2) (-2) (5359344818461 / 5000000000000 : ℝ) (10718689636929 / 10000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hqsub_361 :
    IntervalIntegrable (fun t => Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t)) volume (373 / 200 : ℝ) (593 / 300 : ℝ) ∧
      (311578990027 / 5000000000000 : ℝ) ≤ ∫ t in (373 / 200 : ℝ)..(593 / 300 : ℝ), Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (373 / 200 : ℝ)..(593 / 300 : ℝ), Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ≤ (311578990233 / 5000000000000 : ℝ) :=
  quad_log_div_sub (1 : ℝ) (1 : ℝ) (0 : ℝ) (1 : ℝ) (373 / 200 : ℝ) (593 / 300 : ℝ) (461 / 240 : ℝ) (67 / 1200 : ℝ)
    (701 / 240 : ℝ) (461 / 240 : ℝ) (240 / 701 : ℝ) (240 / 461 : ℝ) (240 / 461 : ℝ) (5359344818461 / 5000000000000 : ℝ) (10718689636929 / 10000000000000 : ℝ) (311578990027 / 5000000000000 : ℝ) (311578990233 / 5000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog_360 (by norm_num [quadLogLo]) (by norm_num [quadLogHi])

private lemma hlog_362 : (11093873618359 / 10000000000000 : ℝ) ≤ Real.log (1213 / 400 : ℝ) ∧ Real.log (1213 / 400 : ℝ) ≤ (11093873618361 / 10000000000000 : ℝ) :=
  log_rat_bounds (1213 / 400 : ℝ) (13 / 2413 : ℝ) (0) (1) (0) (11093873618359 / 10000000000000 : ℝ) (11093873618361 / 10000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hqsub_363 :
    IntervalIntegrable (fun t => Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t)) volume (593 / 300 : ℝ) (1253 / 600 : ℝ) ∧
      (152383290989 / 2500000000000 : ℝ) ≤ ∫ t in (593 / 300 : ℝ)..(1253 / 600 : ℝ), Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (593 / 300 : ℝ)..(1253 / 600 : ℝ), Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ≤ (121906632847 / 2000000000000 : ℝ) :=
  quad_log_div_sub (1 : ℝ) (1 : ℝ) (0 : ℝ) (1 : ℝ) (593 / 300 : ℝ) (1253 / 600 : ℝ) (813 / 400 : ℝ) (67 / 1200 : ℝ)
    (1213 / 400 : ℝ) (813 / 400 : ℝ) (400 / 1213 : ℝ) (400 / 813 : ℝ) (400 / 813 : ℝ) (11093873618359 / 10000000000000 : ℝ) (11093873618361 / 10000000000000 : ℝ) (152383290989 / 2500000000000 : ℝ) (121906632847 / 2000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog_362 (by norm_num [quadLogLo]) (by norm_num [quadLogHi])

private lemma hlog_364 : (11455488841879 / 10000000000000 : ℝ) ≤ Real.log (3773 / 1200 : ℝ) ∧ Real.log (3773 / 1200 : ℝ) ≤ (2291097768377 / 2000000000000 : ℝ) :=
  log_rat_bounds (3773 / 1200 : ℝ) (23 / 7523 : ℝ) (-3) (0) (2) (11455488841879 / 10000000000000 : ℝ) (2291097768377 / 2000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hqsub_365 :
    IntervalIntegrable (fun t => Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t)) volume (1253 / 600 : ℝ) (11 / 5 : ℝ) ∧
      (298310434719 / 5000000000000 : ℝ) ≤ ∫ t in (1253 / 600 : ℝ)..(11 / 5 : ℝ), Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (1253 / 600 : ℝ)..(11 / 5 : ℝ), Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ≤ (596620869631 / 10000000000000 : ℝ) :=
  quad_log_div_sub (1 : ℝ) (1 : ℝ) (0 : ℝ) (1 : ℝ) (1253 / 600 : ℝ) (11 / 5 : ℝ) (2573 / 1200 : ℝ) (67 / 1200 : ℝ)
    (3773 / 1200 : ℝ) (2573 / 1200 : ℝ) (1200 / 3773 : ℝ) (1200 / 2573 : ℝ) (1200 / 2573 : ℝ) (11455488841879 / 10000000000000 : ℝ) (2291097768377 / 2000000000000 : ℝ) (298310434719 / 5000000000000 : ℝ) (596620869631 / 10000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog_364 (by norm_num [quadLogLo]) (by norm_num [quadLogHi])

private lemma hqchain_366 :
    IntervalIntegrable (fun t => Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t)) volume (153 / 100 : ℝ) (263 / 150 : ℝ) ∧
      (330460363993 / 2500000000000 : ℝ) ≤ ∫ t in (153 / 100 : ℝ)..(263 / 150 : ℝ), Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (153 / 100 : ℝ)..(263 / 150 : ℝ), Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ≤ (660920729241 / 5000000000000 : ℝ) :=
  chain_int_bounds hqsub_355 hqsub_357 (by norm_num) (by norm_num)

private lemma hqchain_367 :
    IntervalIntegrable (fun t => Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t)) volume (153 / 100 : ℝ) (373 / 200 : ℝ) ∧
      (979701698863 / 5000000000000 : ℝ) ≤ ∫ t in (153 / 100 : ℝ)..(373 / 200 : ℝ), Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (153 / 100 : ℝ)..(373 / 200 : ℝ), Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ≤ (979701700429 / 5000000000000 : ℝ) :=
  chain_int_bounds hqchain_366 hqsub_359 (by norm_num) (by norm_num)

private lemma hqchain_368 :
    IntervalIntegrable (fun t => Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t)) volume (153 / 100 : ℝ) (593 / 300 : ℝ) ∧
      (129128068889 / 500000000000 : ℝ) ≤ ∫ t in (153 / 100 : ℝ)..(593 / 300 : ℝ), Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (153 / 100 : ℝ)..(593 / 300 : ℝ), Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ≤ (645640345331 / 2500000000000 : ℝ) :=
  chain_int_bounds hqchain_367 hqsub_361 (by norm_num) (by norm_num)

private lemma hqchain_369 :
    IntervalIntegrable (fun t => Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t)) volume (153 / 100 : ℝ) (1253 / 600 : ℝ) ∧
      (399011817717 / 1250000000000 : ℝ) ≤ ∫ t in (153 / 100 : ℝ)..(1253 / 600 : ℝ), Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (153 / 100 : ℝ)..(1253 / 600 : ℝ), Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ≤ (3192094545559 / 10000000000000 : ℝ) :=
  chain_int_bounds hqchain_368 hqsub_363 (by norm_num) (by norm_num)

private lemma hqchain_370 :
    IntervalIntegrable (fun t => Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t)) volume (153 / 100 : ℝ) (11 / 5 : ℝ) ∧
      (1894357705587 / 5000000000000 : ℝ) ≤ ∫ t in (153 / 100 : ℝ)..(11 / 5 : ℝ), Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (153 / 100 : ℝ)..(11 / 5 : ℝ), Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ≤ (378871541519 / 1000000000000 : ℝ) :=
  chain_int_bounds hqchain_369 hqsub_365 (by norm_num) (by norm_num)

private lemma hact_tp_371 :
    IntervalIntegrable (fun t => Real.log ((t + 1) ^ (2 : ℕ) / (4807 / 1000 : ℝ)) / ((5 : ℝ) * t)) volume (153 / 100 : ℝ) (11 / 5 : ℝ) ∧
      (375017579187 / 10000000000000 : ℝ) ≤ ∫ t in (153 / 100 : ℝ)..(11 / 5 : ℝ), Real.log ((t + 1) ^ (2 : ℕ) / (4807 / 1000 : ℝ)) / ((5 : ℝ) * t) :=
  active_t_pow 2 (5 : ℝ) (4807 / 1000 : ℝ) (153 / 100 : ℝ) (11 / 5 : ℝ) (220 / 153 : ℝ) (3140146377823 / 2000000000000 : ℝ) (98129574307 / 62500000000 : ℝ) (726379249919 / 2000000000000 : ℝ) (3631896249603 / 10000000000000 : ℝ)
    (1894357705587 / 5000000000000 : ℝ) (378871541519 / 1000000000000 : ℝ) (375017579187 / 10000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hlog_352 hlog_353 hqchain_370 (by norm_num)

private lemma hterm_351 :
    IntervalIntegrable (fun t => ind (153 / 100 : ℝ) (127 / 50 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) ^ (2 : ℕ) / (4807 / 1000 : ℝ))) volume (1 : ℝ) (11 / 5 : ℝ) ∧
      (375017579187 / 10000000000000 : ℝ) ≤ ∫ t in (1 : ℝ)..(11 / 5 : ℝ), ind (153 / 100 : ℝ) (127 / 50 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) ^ (2 : ℕ) / (4807 / 1000 : ℝ)) :=
  bound_ind_div_active (1 : ℝ) (11 / 5 : ℝ) (153 / 100 : ℝ) (127 / 50 : ℝ) (153 / 100 : ℝ) (11 / 5 : ℝ) (375017579187 / 10000000000000 : ℝ)
    (fun t => (5 : ℝ) * t) (fun t => (t + 1) ^ (2 : ℕ) / (4807 / 1000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (Or.inr rfl) (Or.inl rfl) hact_tp_371

private lemma hlog_373 : (1512927012053 / 1000000000000 : ℝ) ≤ Real.log (227 / 50 : ℝ) ∧ Real.log (227 / 50 : ℝ) ≤ (7564635060267 / 5000000000000 : ℝ) :=
  log_rat_bounds (227 / 50 : ℝ) (1 / 226 : ℝ) (-1) (2) (0) (1512927012053 / 1000000000000 : ℝ) (7564635060267 / 5000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hlog_374 : (1867819910103 / 10000000000000 : ℝ) ≤ Real.log (904033 / 750008 : ℝ) ∧ Real.log (904033 / 750008 : ℝ) ≤ (1867819910107 / 10000000000000 : ℝ) :=
  log_rat_bounds (904033 / 750008 : ℝ) (20117 / 9020213 : ℝ) (1) (1) (-1) (1867819910103 / 10000000000000 : ℝ) (1867819910107 / 10000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hlog_375 : (953271517379 / 10000000000000 : ℝ) ≤ Real.log (135519 / 123197 : ℝ) ∧ Real.log (135519 / 123197 : ℝ) ≤ (476635758693 / 5000000000000 : ℝ) :=
  log_rat_bounds (135519 / 123197 : ℝ) (10276 / 1119049 : ℝ) (0) (3) (-2) (953271517379 / 10000000000000 : ℝ) (476635758693 / 5000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hlog_376 : (4640659591941 / 2500000000000 : ℝ) ≤ Real.log (29279 / 4575 : ℝ) ∧ Real.log (29279 / 4575 : ℝ) ≤ (9281319183887 / 5000000000000 : ℝ) :=
  log_rat_bounds (29279 / 4575 : ℝ) (20981 / 3726731 : ℝ) (-6) (4) (1) (4640659591941 / 2500000000000 : ℝ) (9281319183887 / 5000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hqsub_377 :
    IntervalIntegrable (fun t => Real.log ((57431 / 5000 : ℝ) + (-353 / 100 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t)) volume (750008 / 538325 : ℝ) (2404049 / 1614975 : ℝ) ∧
      (1229213380269 / 10000000000000 : ℝ) ≤ ∫ t in (750008 / 538325 : ℝ)..(2404049 / 1614975 : ℝ), Real.log ((57431 / 5000 : ℝ) + (-353 / 100 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (750008 / 538325 : ℝ)..(2404049 / 1614975 : ℝ), Real.log ((57431 / 5000 : ℝ) + (-353 / 100 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ≤ (307303345349 / 2500000000000 : ℝ) :=
  quad_log_div_sub (57431 / 5000 : ℝ) (-353 / 100 : ℝ) (0 : ℝ) (1 : ℝ) (750008 / 538325 : ℝ) (2404049 / 1614975 : ℝ) (4654073 / 3229950 : ℝ) (101 / 2118 : ℝ)
    (29279 / 4575 : ℝ) (4654073 / 3229950 : ℝ) (-64599 / 117116 : ℝ) (3229950 / 4654073 : ℝ) (3229950 / 4654073 : ℝ) (4640659591941 / 2500000000000 : ℝ) (9281319183887 / 5000000000000 : ℝ) (1229213380269 / 10000000000000 : ℝ) (307303345349 / 2500000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog_376 (by norm_num [quadLogLo]) (by norm_num [quadLogHi])

private lemma hlog_378 : (4505559134651 / 2500000000000 : ℝ) ≤ Real.log (7397 / 1220 : ℝ) ∧ Real.log (7397 / 1220 : ℝ) ≤ (9011118269303 / 5000000000000 : ℝ) :=
  log_rat_bounds (7397 / 1220 : ℝ) (77 / 14717 : ℝ) (1) (1) (0) (4505559134651 / 2500000000000 : ℝ) (9011118269303 / 5000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hqsub_379 :
    IntervalIntegrable (fun t => Real.log ((57431 / 5000 : ℝ) + (-353 / 100 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t)) volume (2404049 / 1614975 : ℝ) (2558074 / 1614975 : ℝ) ∧
      (559641861137 / 5000000000000 : ℝ) ≤ ∫ t in (2404049 / 1614975 : ℝ)..(2558074 / 1614975 : ℝ), Real.log ((57431 / 5000 : ℝ) + (-353 / 100 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (2404049 / 1614975 : ℝ)..(2558074 / 1614975 : ℝ), Real.log ((57431 / 5000 : ℝ) + (-353 / 100 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ≤ (1119283722989 / 10000000000000 : ℝ) :=
  quad_log_div_sub (57431 / 5000 : ℝ) (-353 / 100 : ℝ) (0 : ℝ) (1 : ℝ) (2404049 / 1614975 : ℝ) (2558074 / 1614975 : ℝ) (1654041 / 1076650 : ℝ) (101 / 2118 : ℝ)
    (7397 / 1220 : ℝ) (1654041 / 1076650 : ℝ) (-21533 / 36985 : ℝ) (1076650 / 1654041 : ℝ) (1076650 / 1654041 : ℝ) (4505559134651 / 2500000000000 : ℝ) (9011118269303 / 5000000000000 : ℝ) (559641861137 / 5000000000000 : ℝ) (1119283722989 / 10000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog_378 (by norm_num [quadLogLo]) (by norm_num [quadLogHi])

private lemma hlog_380 : (8725477292459 / 5000000000000 : ℝ) ≤ Real.log (52397 / 9150 : ℝ) ∧ Real.log (52397 / 9150 : ℝ) ≤ (698038183397 / 400000000000 : ℝ) :=
  log_rat_bounds (52397 / 9150 : ℝ) (3713 / 415463 : ℝ) (-3) (2) (1) (8725477292459 / 5000000000000 : ℝ) (698038183397 / 400000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hqsub_381 :
    IntervalIntegrable (fun t => Real.log ((57431 / 5000 : ℝ) + (-353 / 100 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t)) volume (2558074 / 1614975 : ℝ) (2561 / 1525 : ℝ) ∧
      (1020409897213 / 10000000000000 : ℝ) ≤ ∫ t in (2558074 / 1614975 : ℝ)..(2561 / 1525 : ℝ), Real.log ((57431 / 5000 : ℝ) + (-353 / 100 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (2558074 / 1614975 : ℝ)..(2561 / 1525 : ℝ), Real.log ((57431 / 5000 : ℝ) + (-353 / 100 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ≤ (1020409897693 / 10000000000000 : ℝ) :=
  quad_log_div_sub (57431 / 5000 : ℝ) (-353 / 100 : ℝ) (0 : ℝ) (1 : ℝ) (2558074 / 1614975 : ℝ) (2561 / 1525 : ℝ) (5270173 / 3229950 : ℝ) (101 / 2118 : ℝ)
    (52397 / 9150 : ℝ) (5270173 / 3229950 : ℝ) (-64599 / 104794 : ℝ) (3229950 / 5270173 : ℝ) (64599 / 104794 : ℝ) (8725477292459 / 5000000000000 : ℝ) (698038183397 / 400000000000 : ℝ) (1020409897213 / 10000000000000 : ℝ) (1020409897693 / 10000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog_380 (by norm_num [quadLogLo]) (by norm_num [quadLogHi])

private lemma hqchain_382 :
    IntervalIntegrable (fun t => Real.log ((57431 / 5000 : ℝ) + (-353 / 100 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t)) volume (750008 / 538325 : ℝ) (2558074 / 1614975 : ℝ) ∧
      (2348497102543 / 10000000000000 : ℝ) ≤ ∫ t in (750008 / 538325 : ℝ)..(2558074 / 1614975 : ℝ), Real.log ((57431 / 5000 : ℝ) + (-353 / 100 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (750008 / 538325 : ℝ)..(2558074 / 1614975 : ℝ), Real.log ((57431 / 5000 : ℝ) + (-353 / 100 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ≤ (469699420877 / 2000000000000 : ℝ) :=
  chain_int_bounds hqsub_377 hqsub_379 (by norm_num) (by norm_num)

private lemma hqchain_383 :
    IntervalIntegrable (fun t => Real.log ((57431 / 5000 : ℝ) + (-353 / 100 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t)) volume (750008 / 538325 : ℝ) (2561 / 1525 : ℝ) ∧
      (842226749939 / 2500000000000 : ℝ) ≤ ∫ t in (750008 / 538325 : ℝ)..(2561 / 1525 : ℝ), Real.log ((57431 / 5000 : ℝ) + (-353 / 100 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (750008 / 538325 : ℝ)..(2561 / 1525 : ℝ), Real.log ((57431 / 5000 : ℝ) + (-353 / 100 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ≤ (1684453501039 / 5000000000000 : ℝ) :=
  chain_int_bounds hqchain_382 hqsub_381 (by norm_num) (by norm_num)

private lemma hqsub_384 :
    IntervalIntegrable (fun t => Real.log ((57431 / 5000 : ℝ) + (-353 / 100 : ℝ) * t) / ((227 / 50 : ℝ) + (-1 : ℝ) * t)) volume (750008 / 538325 : ℝ) (2404049 / 1614975 : ℝ) ∧
      (571224594877 / 10000000000000 : ℝ) ≤ ∫ t in (750008 / 538325 : ℝ)..(2404049 / 1614975 : ℝ), Real.log ((57431 / 5000 : ℝ) + (-353 / 100 : ℝ) * t) / ((227 / 50 : ℝ) + (-1 : ℝ) * t) ∧
      ∫ t in (750008 / 538325 : ℝ)..(2404049 / 1614975 : ℝ), Real.log ((57431 / 5000 : ℝ) + (-353 / 100 : ℝ) * t) / ((227 / 50 : ℝ) + (-1 : ℝ) * t) ≤ (285612297491 / 5000000000000 : ℝ) :=
  quad_log_div_sub (57431 / 5000 : ℝ) (-353 / 100 : ℝ) (227 / 50 : ℝ) (-1 : ℝ) (750008 / 538325 : ℝ) (2404049 / 1614975 : ℝ) (4654073 / 3229950 : ℝ) (101 / 2118 : ℝ)
    (29279 / 4575 : ℝ) (200198 / 64599 : ℝ) (-64599 / 117116 : ℝ) (-64599 / 200198 : ℝ) (64599 / 117116 : ℝ) (4640659591941 / 2500000000000 : ℝ) (9281319183887 / 5000000000000 : ℝ) (571224594877 / 10000000000000 : ℝ) (285612297491 / 5000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog_376 (by norm_num [quadLogLo]) (by norm_num [quadLogHi])

private lemma hqsub_385 :
    IntervalIntegrable (fun t => Real.log ((57431 / 5000 : ℝ) + (-353 / 100 : ℝ) * t) / ((227 / 50 : ℝ) + (-1 : ℝ) * t)) volume (2404049 / 1614975 : ℝ) (2558074 / 1614975 : ℝ) ∧
      (286098415609 / 5000000000000 : ℝ) ≤ ∫ t in (2404049 / 1614975 : ℝ)..(2558074 / 1614975 : ℝ), Real.log ((57431 / 5000 : ℝ) + (-353 / 100 : ℝ) * t) / ((227 / 50 : ℝ) + (-1 : ℝ) * t) ∧
      ∫ t in (2404049 / 1614975 : ℝ)..(2558074 / 1614975 : ℝ), Real.log ((57431 / 5000 : ℝ) + (-353 / 100 : ℝ) * t) / ((227 / 50 : ℝ) + (-1 : ℝ) * t) ≤ (286098415683 / 5000000000000 : ℝ) :=
  quad_log_div_sub (57431 / 5000 : ℝ) (-353 / 100 : ℝ) (227 / 50 : ℝ) (-1 : ℝ) (2404049 / 1614975 : ℝ) (2558074 / 1614975 : ℝ) (1654041 / 1076650 : ℝ) (101 / 2118 : ℝ)
    (7397 / 1220 : ℝ) (64679 / 21533 : ℝ) (-21533 / 36985 : ℝ) (-21533 / 64679 : ℝ) (21533 / 36985 : ℝ) (4505559134651 / 2500000000000 : ℝ) (9011118269303 / 5000000000000 : ℝ) (286098415609 / 5000000000000 : ℝ) (286098415683 / 5000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog_378 (by norm_num [quadLogLo]) (by norm_num [quadLogHi])

private lemma hqsub_386 :
    IntervalIntegrable (fun t => Real.log ((57431 / 5000 : ℝ) + (-353 / 100 : ℝ) * t) / ((227 / 50 : ℝ) + (-1 : ℝ) * t)) volume (2558074 / 1614975 : ℝ) (2561 / 1525 : ℝ) ∧
      (572218853173 / 10000000000000 : ℝ) ≤ ∫ t in (2558074 / 1614975 : ℝ)..(2561 / 1525 : ℝ), Real.log ((57431 / 5000 : ℝ) + (-353 / 100 : ℝ) * t) / ((227 / 50 : ℝ) + (-1 : ℝ) * t) ∧
      ∫ t in (2558074 / 1614975 : ℝ)..(2561 / 1525 : ℝ), Real.log ((57431 / 5000 : ℝ) + (-353 / 100 : ℝ) * t) / ((227 / 50 : ℝ) + (-1 : ℝ) * t) ≤ (143054713347 / 2500000000000 : ℝ) :=
  quad_log_div_sub (57431 / 5000 : ℝ) (-353 / 100 : ℝ) (227 / 50 : ℝ) (-1 : ℝ) (2558074 / 1614975 : ℝ) (2561 / 1525 : ℝ) (5270173 / 3229950 : ℝ) (101 / 2118 : ℝ)
    (52397 / 9150 : ℝ) (187876 / 64599 : ℝ) (-64599 / 104794 : ℝ) (-64599 / 187876 : ℝ) (64599 / 104794 : ℝ) (8725477292459 / 5000000000000 : ℝ) (698038183397 / 400000000000 : ℝ) (572218853173 / 10000000000000 : ℝ) (143054713347 / 2500000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog_380 (by norm_num [quadLogLo]) (by norm_num [quadLogHi])

private lemma hqchain_387 :
    IntervalIntegrable (fun t => Real.log ((57431 / 5000 : ℝ) + (-353 / 100 : ℝ) * t) / ((227 / 50 : ℝ) + (-1 : ℝ) * t)) volume (750008 / 538325 : ℝ) (2558074 / 1614975 : ℝ) ∧
      (228684285219 / 2000000000000 : ℝ) ≤ ∫ t in (750008 / 538325 : ℝ)..(2558074 / 1614975 : ℝ), Real.log ((57431 / 5000 : ℝ) + (-353 / 100 : ℝ) * t) / ((227 / 50 : ℝ) + (-1 : ℝ) * t) ∧
      ∫ t in (750008 / 538325 : ℝ)..(2558074 / 1614975 : ℝ), Real.log ((57431 / 5000 : ℝ) + (-353 / 100 : ℝ) * t) / ((227 / 50 : ℝ) + (-1 : ℝ) * t) ≤ (285855356587 / 2500000000000 : ℝ) :=
  chain_int_bounds hqsub_384 hqsub_385 (by norm_num) (by norm_num)

private lemma hqchain_388 :
    IntervalIntegrable (fun t => Real.log ((57431 / 5000 : ℝ) + (-353 / 100 : ℝ) * t) / ((227 / 50 : ℝ) + (-1 : ℝ) * t)) volume (750008 / 538325 : ℝ) (2561 / 1525 : ℝ) ∧
      (428910069817 / 2500000000000 : ℝ) ≤ ∫ t in (750008 / 538325 : ℝ)..(2561 / 1525 : ℝ), Real.log ((57431 / 5000 : ℝ) + (-353 / 100 : ℝ) * t) / ((227 / 50 : ℝ) + (-1 : ℝ) * t) ∧
      ∫ t in (750008 / 538325 : ℝ)..(2561 / 1525 : ℝ), Real.log ((57431 / 5000 : ℝ) + (-353 / 100 : ℝ) * t) / ((227 / 50 : ℝ) + (-1 : ℝ) * t) ≤ (214455034967 / 1250000000000 : ℝ) :=
  chain_int_bounds hqchain_387 hqsub_386 (by norm_num) (by norm_num)

private lemma hlog_389 : (2211688986021 / 2000000000000 : ℝ) ≤ Real.log (160003 / 52950 : ℝ) ∧ Real.log (160003 / 52950 : ℝ) ≤ (11058444930107 / 10000000000000 : ℝ) :=
  log_rat_bounds (160003 / 52950 : ℝ) (1153 / 318853 : ℝ) (0) (1) (0) (2211688986021 / 2000000000000 : ℝ) (11058444930107 / 10000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hqsub_390 :
    IntervalIntegrable (fun t => Real.log ((4086 / 625 : ℝ) + (-61 / 25 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t)) volume (750008 / 538325 : ℝ) (2404049 / 1614975 : ℝ) ∧
      (146467240967 / 2000000000000 : ℝ) ≤ ∫ t in (750008 / 538325 : ℝ)..(2404049 / 1614975 : ℝ), Real.log ((4086 / 625 : ℝ) + (-61 / 25 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (750008 / 538325 : ℝ)..(2404049 / 1614975 : ℝ), Real.log ((4086 / 625 : ℝ) + (-61 / 25 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ≤ (366168103573 / 5000000000000 : ℝ) :=
  quad_log_div_sub (4086 / 625 : ℝ) (-61 / 25 : ℝ) (0 : ℝ) (1 : ℝ) (750008 / 538325 : ℝ) (2404049 / 1614975 : ℝ) (4654073 / 3229950 : ℝ) (101 / 2118 : ℝ)
    (160003 / 52950 : ℝ) (4654073 / 3229950 : ℝ) (-2118 / 2623 : ℝ) (3229950 / 4654073 : ℝ) (2118 / 2623 : ℝ) (2211688986021 / 2000000000000 : ℝ) (11058444930107 / 10000000000000 : ℝ) (146467240967 / 2000000000000 : ℝ) (366168103573 / 5000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog_389 (by norm_num [quadLogLo]) (by norm_num [quadLogHi])

private lemma hlog_391 : (2051412940163 / 2000000000000 : ℝ) ≤ Real.log (49227 / 17650 : ℝ) ∧ Real.log (49227 / 17650 : ℝ) ≤ (10257064700821 / 10000000000000 : ℝ) :=
  log_rat_bounds (49227 / 17650 : ℝ) (1793 / 884293 : ℝ) (0) (-2) (2) (2051412940163 / 2000000000000 : ℝ) (10257064700821 / 10000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hqsub_392 :
    IntervalIntegrable (fun t => Real.log ((4086 / 625 : ℝ) + (-61 / 25 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t)) volume (2404049 / 1614975 : ℝ) (2558074 / 1614975 : ℝ) ∧
      (159263510563 / 2500000000000 : ℝ) ≤ ∫ t in (2404049 / 1614975 : ℝ)..(2558074 / 1614975 : ℝ), Real.log ((4086 / 625 : ℝ) + (-61 / 25 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (2404049 / 1614975 : ℝ)..(2558074 / 1614975 : ℝ), Real.log ((4086 / 625 : ℝ) + (-61 / 25 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ≤ (39815877851 / 625000000000 : ℝ) :=
  quad_log_div_sub (4086 / 625 : ℝ) (-61 / 25 : ℝ) (0 : ℝ) (1 : ℝ) (2404049 / 1614975 : ℝ) (2558074 / 1614975 : ℝ) (1654041 / 1076650 : ℝ) (101 / 2118 : ℝ)
    (49227 / 17650 : ℝ) (1654041 / 1076650 : ℝ) (-706 / 807 : ℝ) (1076650 / 1654041 : ℝ) (706 / 807 : ℝ) (2051412940163 / 2000000000000 : ℝ) (10257064700821 / 10000000000000 : ℝ) (159263510563 / 2500000000000 : ℝ) (39815877851 / 625000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog_391 (by norm_num [quadLogLo]) (by norm_num [quadLogHi])

private lemma hlog_393 : (9385824360759 / 10000000000000 : ℝ) ≤ Real.log (135359 / 52950 : ℝ) ∧ Real.log (135359 / 52950 : ℝ) ≤ (9385824360767 / 10000000000000 : ℝ) :=
  log_rat_bounds (135359 / 52950 : ℝ) (21269 / 4310219 : ℝ) (-5) (4) (0) (9385824360759 / 10000000000000 : ℝ) (9385824360767 / 10000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hqsub_394 :
    IntervalIntegrable (fun t => Real.log ((4086 / 625 : ℝ) + (-61 / 25 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t)) volume (2558074 / 1614975 : ℝ) (2561 / 1525 : ℝ) ∧
      (274415009661 / 5000000000000 : ℝ) ≤ ∫ t in (2558074 / 1614975 : ℝ)..(2561 / 1525 : ℝ), Real.log ((4086 / 625 : ℝ) + (-61 / 25 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (2558074 / 1614975 : ℝ)..(2561 / 1525 : ℝ), Real.log ((4086 / 625 : ℝ) + (-61 / 25 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ≤ (21953200983 / 400000000000 : ℝ) :=
  quad_log_div_sub (4086 / 625 : ℝ) (-61 / 25 : ℝ) (0 : ℝ) (1 : ℝ) (2558074 / 1614975 : ℝ) (2561 / 1525 : ℝ) (5270173 / 3229950 : ℝ) (101 / 2118 : ℝ)
    (135359 / 52950 : ℝ) (5270173 / 3229950 : ℝ) (-2118 / 2219 : ℝ) (3229950 / 5270173 : ℝ) (2118 / 2219 : ℝ) (9385824360759 / 10000000000000 : ℝ) (9385824360767 / 10000000000000 : ℝ) (274415009661 / 5000000000000 : ℝ) (21953200983 / 400000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog_393 (by norm_num [quadLogLo]) (by norm_num [quadLogHi])

private lemma hqchain_395 :
    IntervalIntegrable (fun t => Real.log ((4086 / 625 : ℝ) + (-61 / 25 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t)) volume (750008 / 538325 : ℝ) (2558074 / 1614975 : ℝ) ∧
      (1369390247087 / 10000000000000 : ℝ) ≤ ∫ t in (750008 / 538325 : ℝ)..(2558074 / 1614975 : ℝ), Real.log ((4086 / 625 : ℝ) + (-61 / 25 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (750008 / 538325 : ℝ)..(2558074 / 1614975 : ℝ), Real.log ((4086 / 625 : ℝ) + (-61 / 25 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ≤ (684695126381 / 5000000000000 : ℝ) :=
  chain_int_bounds hqsub_390 hqsub_392 (by norm_num) (by norm_num)

private lemma hqchain_396 :
    IntervalIntegrable (fun t => Real.log ((4086 / 625 : ℝ) + (-61 / 25 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t)) volume (750008 / 538325 : ℝ) (2561 / 1525 : ℝ) ∧
      (1918220266409 / 10000000000000 : ℝ) ≤ ∫ t in (750008 / 538325 : ℝ)..(2561 / 1525 : ℝ), Real.log ((4086 / 625 : ℝ) + (-61 / 25 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (750008 / 538325 : ℝ)..(2561 / 1525 : ℝ), Real.log ((4086 / 625 : ℝ) + (-61 / 25 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ≤ (1918220277337 / 10000000000000 : ℝ) :=
  chain_int_bounds hqchain_395 hqsub_394 (by norm_num) (by norm_num)

private lemma hqsub_397 :
    IntervalIntegrable (fun t => Real.log ((4086 / 625 : ℝ) + (-61 / 25 : ℝ) * t) / ((227 / 50 : ℝ) + (-1 : ℝ) * t)) volume (750008 / 538325 : ℝ) (2404049 / 1614975 : ℝ) ∧
      (68041688943 / 2000000000000 : ℝ) ≤ ∫ t in (750008 / 538325 : ℝ)..(2404049 / 1614975 : ℝ), Real.log ((4086 / 625 : ℝ) + (-61 / 25 : ℝ) * t) / ((227 / 50 : ℝ) + (-1 : ℝ) * t) ∧
      ∫ t in (750008 / 538325 : ℝ)..(2404049 / 1614975 : ℝ), Real.log ((4086 / 625 : ℝ) + (-61 / 25 : ℝ) * t) / ((227 / 50 : ℝ) + (-1 : ℝ) * t) ≤ (8505211143 / 250000000000 : ℝ) :=
  quad_log_div_sub (4086 / 625 : ℝ) (-61 / 25 : ℝ) (227 / 50 : ℝ) (-1 : ℝ) (750008 / 538325 : ℝ) (2404049 / 1614975 : ℝ) (4654073 / 3229950 : ℝ) (101 / 2118 : ℝ)
    (160003 / 52950 : ℝ) (200198 / 64599 : ℝ) (-2118 / 2623 : ℝ) (-64599 / 200198 : ℝ) (2118 / 2623 : ℝ) (2211688986021 / 2000000000000 : ℝ) (11058444930107 / 10000000000000 : ℝ) (68041688943 / 2000000000000 : ℝ) (8505211143 / 250000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog_389 (by norm_num [quadLogLo]) (by norm_num [quadLogHi])

private lemma hqsub_398 :
    IntervalIntegrable (fun t => Real.log ((4086 / 625 : ℝ) + (-61 / 25 : ℝ) * t) / ((227 / 50 : ℝ) + (-1 : ℝ) * t)) volume (2404049 / 1614975 : ℝ) (2558074 / 1614975 : ℝ) ∧
      (65108812987 / 2000000000000 : ℝ) ≤ ∫ t in (2404049 / 1614975 : ℝ)..(2558074 / 1614975 : ℝ), Real.log ((4086 / 625 : ℝ) + (-61 / 25 : ℝ) * t) / ((227 / 50 : ℝ) + (-1 : ℝ) * t) ∧
      ∫ t in (2404049 / 1614975 : ℝ)..(2558074 / 1614975 : ℝ), Real.log ((4086 / 625 : ℝ) + (-61 / 25 : ℝ) * t) / ((227 / 50 : ℝ) + (-1 : ℝ) * t) ≤ (325544066611 / 10000000000000 : ℝ) :=
  quad_log_div_sub (4086 / 625 : ℝ) (-61 / 25 : ℝ) (227 / 50 : ℝ) (-1 : ℝ) (2404049 / 1614975 : ℝ) (2558074 / 1614975 : ℝ) (1654041 / 1076650 : ℝ) (101 / 2118 : ℝ)
    (49227 / 17650 : ℝ) (64679 / 21533 : ℝ) (-706 / 807 : ℝ) (-21533 / 64679 : ℝ) (706 / 807 : ℝ) (2051412940163 / 2000000000000 : ℝ) (10257064700821 / 10000000000000 : ℝ) (65108812987 / 2000000000000 : ℝ) (325544066611 / 10000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog_391 (by norm_num [quadLogLo]) (by norm_num [quadLogHi])

private lemma hqsub_399 :
    IntervalIntegrable (fun t => Real.log ((4086 / 625 : ℝ) + (-61 / 25 : ℝ) * t) / ((227 / 50 : ℝ) + (-1 : ℝ) * t)) volume (2558074 / 1614975 : ℝ) (2561 / 1525 : ℝ) ∧
      (3845263733 / 125000000000 : ℝ) ≤ ∫ t in (2558074 / 1614975 : ℝ)..(2561 / 1525 : ℝ), Real.log ((4086 / 625 : ℝ) + (-61 / 25 : ℝ) * t) / ((227 / 50 : ℝ) + (-1 : ℝ) * t) ∧
      ∫ t in (2558074 / 1614975 : ℝ)..(2561 / 1525 : ℝ), Real.log ((4086 / 625 : ℝ) + (-61 / 25 : ℝ) * t) / ((227 / 50 : ℝ) + (-1 : ℝ) * t) ≤ (153810550779 / 5000000000000 : ℝ) :=
  quad_log_div_sub (4086 / 625 : ℝ) (-61 / 25 : ℝ) (227 / 50 : ℝ) (-1 : ℝ) (2558074 / 1614975 : ℝ) (2561 / 1525 : ℝ) (5270173 / 3229950 : ℝ) (101 / 2118 : ℝ)
    (135359 / 52950 : ℝ) (187876 / 64599 : ℝ) (-2118 / 2219 : ℝ) (-64599 / 187876 : ℝ) (2118 / 2219 : ℝ) (9385824360759 / 10000000000000 : ℝ) (9385824360767 / 10000000000000 : ℝ) (3845263733 / 125000000000 : ℝ) (153810550779 / 5000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog_393 (by norm_num [quadLogLo]) (by norm_num [quadLogHi])

private lemma hqchain_400 :
    IntervalIntegrable (fun t => Real.log ((4086 / 625 : ℝ) + (-61 / 25 : ℝ) * t) / ((227 / 50 : ℝ) + (-1 : ℝ) * t)) volume (750008 / 538325 : ℝ) (2558074 / 1614975 : ℝ) ∧
      (13315050193 / 200000000000 : ℝ) ≤ ∫ t in (750008 / 538325 : ℝ)..(2558074 / 1614975 : ℝ), Real.log ((4086 / 625 : ℝ) + (-61 / 25 : ℝ) * t) / ((227 / 50 : ℝ) + (-1 : ℝ) * t) ∧
      ∫ t in (750008 / 538325 : ℝ)..(2558074 / 1614975 : ℝ), Real.log ((4086 / 625 : ℝ) + (-61 / 25 : ℝ) * t) / ((227 / 50 : ℝ) + (-1 : ℝ) * t) ≤ (665752512331 / 10000000000000 : ℝ) :=
  chain_int_bounds hqsub_397 hqsub_398 (by norm_num) (by norm_num)

private lemma hqchain_401 :
    IntervalIntegrable (fun t => Real.log ((4086 / 625 : ℝ) + (-61 / 25 : ℝ) * t) / ((227 / 50 : ℝ) + (-1 : ℝ) * t)) volume (750008 / 538325 : ℝ) (2561 / 1525 : ℝ) ∧
      (97337360829 / 1000000000000 : ℝ) ≤ ∫ t in (750008 / 538325 : ℝ)..(2561 / 1525 : ℝ), Real.log ((4086 / 625 : ℝ) + (-61 / 25 : ℝ) * t) / ((227 / 50 : ℝ) + (-1 : ℝ) * t) ∧
      ∫ t in (750008 / 538325 : ℝ)..(2561 / 1525 : ℝ), Real.log ((4086 / 625 : ℝ) + (-61 / 25 : ℝ) * t) / ((227 / 50 : ℝ) + (-1 : ℝ) * t) ≤ (973373613889 / 10000000000000 : ℝ) :=
  chain_int_bounds hqchain_400 hqsub_399 (by norm_num) (by norm_num)

private lemma hact_q6_402 :
    IntervalIntegrable (fun t => Real.log ((227 / 50 : ℝ) ^ (2 : ℕ) / (((353 / 100 : ℝ) * (227 / 50 : ℝ) - (227 / 50 : ℝ) - (353 / 100 : ℝ) * t) * ((61 / 25 : ℝ) * (227 / 50 : ℝ) - (227 / 50 : ℝ) - (61 / 25 : ℝ) * t))) / (5 * t * (1 - t / (227 / 50 : ℝ)))) volume (750008 / 538325 : ℝ) (2561 / 1525 : ℝ) ∧
      (22402787007 / 2000000000000 : ℝ) ≤ ∫ t in (750008 / 538325 : ℝ)..(2561 / 1525 : ℝ), Real.log ((227 / 50 : ℝ) ^ (2 : ℕ) / (((353 / 100 : ℝ) * (227 / 50 : ℝ) - (227 / 50 : ℝ) - (353 / 100 : ℝ) * t) * ((61 / 25 : ℝ) * (227 / 50 : ℝ) - (227 / 50 : ℝ) - (61 / 25 : ℝ) * t))) / (5 * t * (1 - t / (227 / 50 : ℝ))) :=
  active_q_6 (227 / 50 : ℝ) (353 / 100 : ℝ) (61 / 25 : ℝ) (57431 / 5000 : ℝ) (-353 / 100 : ℝ) (4086 / 625 : ℝ) (-61 / 25 : ℝ) (750008 / 538325 : ℝ) (2561 / 1525 : ℝ) (904033 / 750008 : ℝ) (135519 / 123197 : ℝ)
    (1512927012053 / 1000000000000 : ℝ) (7564635060267 / 5000000000000 : ℝ) (1867819910103 / 10000000000000 : ℝ) (1867819910107 / 10000000000000 : ℝ) (953271517379 / 10000000000000 : ℝ) (476635758693 / 5000000000000 : ℝ)
    (842226749939 / 2500000000000 : ℝ) (1684453501039 / 5000000000000 : ℝ) (428910069817 / 2500000000000 : ℝ) (214455034967 / 1250000000000 : ℝ) (1918220266409 / 10000000000000 : ℝ) (1918220277337 / 10000000000000 : ℝ) (97337360829 / 1000000000000 : ℝ) (973373613889 / 10000000000000 : ℝ) (22402787007 / 2000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog_373 hlog_374 hlog_375 hqchain_383 hqchain_388 hqchain_396 hqchain_401 (by norm_num)

private lemma hterm_372 :
    IntervalIntegrable (fun t => ind (750008 / 538325 : ℝ) (2561 / 1525 : ℝ) t / (5 * t * (1 - t / (227 / 50 : ℝ))) * Real.log ((227 / 50 : ℝ) ^ (2 : ℕ) / (((353 / 100 : ℝ) * (227 / 50 : ℝ) - (227 / 50 : ℝ) - (353 / 100 : ℝ) * t) * ((61 / 25 : ℝ) * (227 / 50 : ℝ) - (227 / 50 : ℝ) - (61 / 25 : ℝ) * t)))) volume (1 : ℝ) (11 / 5 : ℝ) ∧
      (22402787007 / 2000000000000 : ℝ) ≤ ∫ t in (1 : ℝ)..(11 / 5 : ℝ), ind (750008 / 538325 : ℝ) (2561 / 1525 : ℝ) t / (5 * t * (1 - t / (227 / 50 : ℝ))) * Real.log ((227 / 50 : ℝ) ^ (2 : ℕ) / (((353 / 100 : ℝ) * (227 / 50 : ℝ) - (227 / 50 : ℝ) - (353 / 100 : ℝ) * t) * ((61 / 25 : ℝ) * (227 / 50 : ℝ) - (227 / 50 : ℝ) - (61 / 25 : ℝ) * t))) :=
  bound_ind_div_active (1 : ℝ) (11 / 5 : ℝ) (750008 / 538325 : ℝ) (2561 / 1525 : ℝ) (750008 / 538325 : ℝ) (2561 / 1525 : ℝ) (22402787007 / 2000000000000 : ℝ)
    (fun t => 5 * t * (1 - t / (227 / 50 : ℝ))) (fun t => (227 / 50 : ℝ) ^ (2 : ℕ) / (((353 / 100 : ℝ) * (227 / 50 : ℝ) - (227 / 50 : ℝ) - (353 / 100 : ℝ) * t) * ((61 / 25 : ℝ) * (227 / 50 : ℝ) - (227 / 50 : ℝ) - (61 / 25 : ℝ) * t)))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (Or.inr rfl) (Or.inr rfl) hact_q6_402

private lemma hlog_404 : (53564843579 / 10000000000000 : ℝ) ≤ Real.log (52715529 / 52433914 : ℝ) ∧ Real.log (52715529 / 52433914 : ℝ) ≤ (2678242179 / 500000000000 : ℝ) :=
  log_rat_bounds (52715529 / 52433914 : ℝ) (281615 / 105149443 : ℝ) (0) (0) (0) (53564843579 / 10000000000000 : ℝ) (2678242179 / 500000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hlog_405 : (3083921 / 976562500 : ℝ) ≤ Real.log (17863565 / 17807242 : ℝ) ∧ Real.log (17863565 / 17807242 : ℝ) ≤ (31579351041 / 10000000000000 : ℝ) :=
  log_rat_bounds (17863565 / 17807242 : ℝ) (56323 / 35670807 : ℝ) (0) (0) (0) (3083921 / 976562500 : ℝ) (31579351041 / 10000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hlog_406 : (618502284087 / 1000000000000 : ℝ) ≤ Real.log (23181667 / 12489140 : ℝ) ∧ Real.log (23181667 / 12489140 : ℝ) ≤ (6185022840877 / 10000000000000 : ℝ) :=
  log_rat_bounds (23181667 / 12489140 : ℝ) (1448009 / 1250362009 : ℝ) (1) (-3) (2) (618502284087 / 1000000000000 : ℝ) (6185022840877 / 10000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hqsub_407 :
    IntervalIntegrable (fun t => Real.log ((177 / 50 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t)) volume (2561 / 1525 : ℝ) (864189 / 511850 : ℝ) ∧
      (6626008317 / 2000000000000 : ℝ) ≤ ∫ t in (2561 / 1525 : ℝ)..(864189 / 511850 : ℝ), Real.log ((177 / 50 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (2561 / 1525 : ℝ)..(864189 / 511850 : ℝ), Real.log ((177 / 50 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ≤ (16565020793 / 5000000000000 : ℝ) :=
  quad_log_div_sub (177 / 50 : ℝ) (-1 : ℝ) (0 : ℝ) (1 : ℝ) (2561 / 1525 : ℝ) (864189 / 511850 : ℝ) (105149443 / 62445700 : ℝ) (56323 / 12489140 : ℝ)
    (23181667 / 12489140 : ℝ) (105149443 / 62445700 : ℝ) (-12489140 / 23181667 : ℝ) (62445700 / 105149443 : ℝ) (62445700 / 105149443 : ℝ) (618502284087 / 1000000000000 : ℝ) (6185022840877 / 10000000000000 : ℝ) (6626008317 / 2000000000000 : ℝ) (16565020793 / 5000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog_406 (by norm_num [quadLogLo]) (by norm_num [quadLogHi])

private lemma hqsub_408 :
    IntervalIntegrable (fun t => Real.log ((177 / 50 : ℝ) + (-1 : ℝ) * t) / ((227 / 50 : ℝ) + (-1 : ℝ) * t)) volume (2561 / 1525 : ℝ) (864189 / 511850 : ℝ) ∧
      (3906365859 / 2000000000000 : ℝ) ≤ ∫ t in (2561 / 1525 : ℝ)..(864189 / 511850 : ℝ), Real.log ((177 / 50 : ℝ) + (-1 : ℝ) * t) / ((227 / 50 : ℝ) + (-1 : ℝ) * t) ∧
      ∫ t in (2561 / 1525 : ℝ)..(864189 / 511850 : ℝ), Real.log ((177 / 50 : ℝ) + (-1 : ℝ) * t) / ((227 / 50 : ℝ) + (-1 : ℝ) * t) ≤ (1220739331 / 625000000000 : ℝ) :=
  quad_log_div_sub (177 / 50 : ℝ) (-1 : ℝ) (227 / 50 : ℝ) (-1 : ℝ) (2561 / 1525 : ℝ) (864189 / 511850 : ℝ) (105149443 / 62445700 : ℝ) (56323 / 12489140 : ℝ)
    (23181667 / 12489140 : ℝ) (35670807 / 12489140 : ℝ) (-12489140 / 23181667 : ℝ) (-12489140 / 35670807 : ℝ) (12489140 / 23181667 : ℝ) (618502284087 / 1000000000000 : ℝ) (6185022840877 / 10000000000000 : ℝ) (3906365859 / 2000000000000 : ℝ) (1220739331 / 625000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog_406 (by norm_num [quadLogLo]) (by norm_num [quadLogHi])

private lemma hlog_409 : (4280976718159 / 2500000000000 : ℝ) ≤ Real.log (19608287 / 3538000 : ℝ) ∧ Real.log (19608287 / 3538000 : ℝ) ≤ (8561953436321 / 5000000000000 : ℝ) :=
  log_rat_bounds (19608287 / 3538000 : ℝ) (503087 / 38713487 : ℝ) (0) (3) (-1) (4280976718159 / 2500000000000 : ℝ) (8561953436321 / 5000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hqsub_410 :
    IntervalIntegrable (fun t => Real.log ((57431 / 5000 : ℝ) + (-353 / 100 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t)) volume (2561 / 1525 : ℝ) (864189 / 511850 : ℝ) ∧
      (9172400301 / 1000000000000 : ℝ) ≤ ∫ t in (2561 / 1525 : ℝ)..(864189 / 511850 : ℝ), Real.log ((57431 / 5000 : ℝ) + (-353 / 100 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (2561 / 1525 : ℝ)..(864189 / 511850 : ℝ), Real.log ((57431 / 5000 : ℝ) + (-353 / 100 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ≤ (91724003011 / 10000000000000 : ℝ) :=
  quad_log_div_sub (57431 / 5000 : ℝ) (-353 / 100 : ℝ) (0 : ℝ) (1 : ℝ) (2561 / 1525 : ℝ) (864189 / 511850 : ℝ) (105149443 / 62445700 : ℝ) (56323 / 12489140 : ℝ)
    (19608287 / 3538000 : ℝ) (105149443 / 62445700 : ℝ) (-12489140 / 19608287 : ℝ) (62445700 / 105149443 : ℝ) (12489140 / 19608287 : ℝ) (4280976718159 / 2500000000000 : ℝ) (8561953436321 / 5000000000000 : ℝ) (9172400301 / 1000000000000 : ℝ) (91724003011 / 10000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog_409 (by norm_num [quadLogLo]) (by norm_num [quadLogHi])

private lemma hqsub_411 :
    IntervalIntegrable (fun t => Real.log ((57431 / 5000 : ℝ) + (-353 / 100 : ℝ) * t) / ((227 / 50 : ℝ) + (-1 : ℝ) * t)) volume (2561 / 1525 : ℝ) (864189 / 511850 : ℝ) ∧
      (54076095463 / 10000000000000 : ℝ) ≤ ∫ t in (2561 / 1525 : ℝ)..(864189 / 511850 : ℝ), Real.log ((57431 / 5000 : ℝ) + (-353 / 100 : ℝ) * t) / ((227 / 50 : ℝ) + (-1 : ℝ) * t) ∧
      ∫ t in (2561 / 1525 : ℝ)..(864189 / 511850 : ℝ), Real.log ((57431 / 5000 : ℝ) + (-353 / 100 : ℝ) * t) / ((227 / 50 : ℝ) + (-1 : ℝ) * t) ≤ (6759511933 / 1250000000000 : ℝ) :=
  quad_log_div_sub (57431 / 5000 : ℝ) (-353 / 100 : ℝ) (227 / 50 : ℝ) (-1 : ℝ) (2561 / 1525 : ℝ) (864189 / 511850 : ℝ) (105149443 / 62445700 : ℝ) (56323 / 12489140 : ℝ)
    (19608287 / 3538000 : ℝ) (35670807 / 12489140 : ℝ) (-12489140 / 19608287 : ℝ) (-12489140 / 35670807 : ℝ) (12489140 / 19608287 : ℝ) (4280976718159 / 2500000000000 : ℝ) (8561953436321 / 5000000000000 : ℝ) (54076095463 / 10000000000000 : ℝ) (6759511933 / 1250000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog_409 (by norm_num [quadLogLo]) (by norm_num [quadLogHi])

private lemma hact_q7_412 :
    IntervalIntegrable (fun t => Real.log ((227 / 50 : ℝ) * ((227 / 50 : ℝ) - 1 - t) / ((353 / 100 : ℝ) * (227 / 50 : ℝ) - (227 / 50 : ℝ) - (353 / 100 : ℝ) * t)) / (5 * t * (1 - t / (227 / 50 : ℝ)))) volume (2561 / 1525 : ℝ) (864189 / 511850 : ℝ) ∧
      (891968109 / 1250000000000 : ℝ) ≤ ∫ t in (2561 / 1525 : ℝ)..(864189 / 511850 : ℝ), Real.log ((227 / 50 : ℝ) * ((227 / 50 : ℝ) - 1 - t) / ((353 / 100 : ℝ) * (227 / 50 : ℝ) - (227 / 50 : ℝ) - (353 / 100 : ℝ) * t)) / (5 * t * (1 - t / (227 / 50 : ℝ))) :=
  active_q_7 (227 / 50 : ℝ) (353 / 100 : ℝ) (177 / 50 : ℝ) (57431 / 5000 : ℝ) (-353 / 100 : ℝ) (2561 / 1525 : ℝ) (864189 / 511850 : ℝ) (52715529 / 52433914 : ℝ) (17863565 / 17807242 : ℝ)
    (1512927012053 / 1000000000000 : ℝ) (7564635060267 / 5000000000000 : ℝ) (53564843579 / 10000000000000 : ℝ) (2678242179 / 500000000000 : ℝ) (3083921 / 976562500 : ℝ) (31579351041 / 10000000000000 : ℝ)
    (6626008317 / 2000000000000 : ℝ) (16565020793 / 5000000000000 : ℝ) (3906365859 / 2000000000000 : ℝ) (1220739331 / 625000000000 : ℝ) (9172400301 / 1000000000000 : ℝ) (91724003011 / 10000000000000 : ℝ) (54076095463 / 10000000000000 : ℝ) (6759511933 / 1250000000000 : ℝ) (891968109 / 1250000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog_373 hlog_404 hlog_405 hqsub_407 hqsub_408 hqsub_410 hqsub_411 (by norm_num)

private lemma hterm_403 :
    IntervalIntegrable (fun t => ind (2561 / 1525 : ℝ) (864189 / 511850 : ℝ) t / (5 * t * (1 - t / (227 / 50 : ℝ))) * Real.log ((227 / 50 : ℝ) * ((227 / 50 : ℝ) - 1 - t) / ((353 / 100 : ℝ) * (227 / 50 : ℝ) - (227 / 50 : ℝ) - (353 / 100 : ℝ) * t))) volume (1 : ℝ) (11 / 5 : ℝ) ∧
      (891968109 / 1250000000000 : ℝ) ≤ ∫ t in (1 : ℝ)..(11 / 5 : ℝ), ind (2561 / 1525 : ℝ) (864189 / 511850 : ℝ) t / (5 * t * (1 - t / (227 / 50 : ℝ))) * Real.log ((227 / 50 : ℝ) * ((227 / 50 : ℝ) - 1 - t) / ((353 / 100 : ℝ) * (227 / 50 : ℝ) - (227 / 50 : ℝ) - (353 / 100 : ℝ) * t)) :=
  bound_ind_div_active (1 : ℝ) (11 / 5 : ℝ) (2561 / 1525 : ℝ) (864189 / 511850 : ℝ) (2561 / 1525 : ℝ) (864189 / 511850 : ℝ) (891968109 / 1250000000000 : ℝ)
    (fun t => 5 * t * (1 - t / (227 / 50 : ℝ))) (fun t => (227 / 50 : ℝ) * ((227 / 50 : ℝ) - 1 - t) / ((353 / 100 : ℝ) * (227 / 50 : ℝ) - (227 / 50 : ℝ) - (353 / 100 : ℝ) * t))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (Or.inr rfl) (Or.inr rfl) hact_q7_412

private lemma hlog_414 : (904520610563 / 5000000000000 : ℝ) ≤ Real.log (423 / 353 : ℝ) ∧ Real.log (423 / 353 : ℝ) ≤ (1809041221133 / 10000000000000 : ℝ) :=
  log_rat_bounds (423 / 353 : ℝ) (125 / 22717 : ℝ) (5) (-3) (0) (904520610563 / 5000000000000 : ℝ) (1809041221133 / 10000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hlog_415 : (934705132553 / 10000000000000 : ℝ) ≤ Real.log (706 / 643 : ℝ) ∧ Real.log (706 / 643 : ℝ) ≤ (11683814157 / 125000000000 : ℝ) :=
  log_rat_bounds (706 / 643 : ℝ) (289 / 35011 : ℝ) (0) (3) (-2) (934705132553 / 10000000000000 : ℝ) (11683814157 / 125000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hlog_416 : (7413653064109 / 5000000000000 : ℝ) ≤ Real.log (31099 / 7060 : ℝ) ∧ Real.log (31099 / 7060 : ℝ) ≤ (7413653064113 / 5000000000000 : ℝ) :=
  log_rat_bounds (31099 / 7060 : ℝ) (2999 / 307991 : ℝ) (2) (3) (-2) (7413653064109 / 5000000000000 : ℝ) (7413653064113 / 5000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hqsub_417 :
    IntervalIntegrable (fun t => Real.log ((4313 / 500 : ℝ) + (-29 / 10 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t)) volume (2043 / 1450 : ℝ) (768849 / 511850 : ℝ) ∧
      (474581831423 / 5000000000000 : ℝ) ≤ ∫ t in (2043 / 1450 : ℝ)..(768849 / 511850 : ℝ), Real.log ((4313 / 500 : ℝ) + (-29 / 10 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (2043 / 1450 : ℝ)..(768849 / 511850 : ℝ), Real.log ((4313 / 500 : ℝ) + (-29 / 10 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ≤ (189832732739 / 2000000000000 : ℝ) :=
  quad_log_div_sub (4313 / 500 : ℝ) (-29 / 10 : ℝ) (0 : ℝ) (1 : ℝ) (2043 / 1450 : ℝ) (768849 / 511850 : ℝ) (372507 / 255925 : ℝ) (4767 / 102370 : ℝ)
    (31099 / 7060 : ℝ) (372507 / 255925 : ℝ) (-20474 / 31099 : ℝ) (255925 / 372507 : ℝ) (255925 / 372507 : ℝ) (7413653064109 / 5000000000000 : ℝ) (7413653064113 / 5000000000000 : ℝ) (474581831423 / 5000000000000 : ℝ) (189832732739 / 2000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog_416 (by norm_num [quadLogLo]) (by norm_num [quadLogHi])

private lemma hlog_418 : (3548641246993 / 2500000000000 : ℝ) ≤ Real.log (145961 / 35300 : ℝ) ∧ Real.log (145961 / 35300 : ℝ) ≤ (709728249399 / 500000000000 : ℝ) :=
  log_rat_bounds (145961 / 35300 : ℝ) (1498 / 144463 : ℝ) (-2) (4) (-1) (3548641246993 / 2500000000000 : ℝ) (709728249399 / 500000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hqsub_419 :
    IntervalIntegrable (fun t => Real.log ((4313 / 500 : ℝ) + (-29 / 10 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t)) volume (768849 / 511850 : ℝ) (816519 / 511850 : ℝ) ∧
      (53373277969 / 625000000000 : ℝ) ≤ ∫ t in (768849 / 511850 : ℝ)..(816519 / 511850 : ℝ), Real.log ((4313 / 500 : ℝ) + (-29 / 10 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (768849 / 511850 : ℝ)..(816519 / 511850 : ℝ), Real.log ((4313 / 500 : ℝ) + (-29 / 10 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ≤ (170794489667 / 2000000000000 : ℝ) :=
  quad_log_div_sub (4313 / 500 : ℝ) (-29 / 10 : ℝ) (0 : ℝ) (1 : ℝ) (768849 / 511850 : ℝ) (816519 / 511850 : ℝ) (396342 / 255925 : ℝ) (4767 / 102370 : ℝ)
    (145961 / 35300 : ℝ) (396342 / 255925 : ℝ) (-102370 / 145961 : ℝ) (255925 / 396342 : ℝ) (102370 / 145961 : ℝ) (3548641246993 / 2500000000000 : ℝ) (709728249399 / 500000000000 : ℝ) (53373277969 / 625000000000 : ℝ) (170794489667 / 2000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog_418 (by norm_num [quadLogLo]) (by norm_num [quadLogHi])

private lemma hlog_420 : (3379766772737 / 2500000000000 : ℝ) ≤ Real.log (136427 / 35300 : ℝ) ∧ Real.log (136427 / 35300 : ℝ) ≤ (3379766772739 / 2500000000000 : ℝ) :=
  log_rat_bounds (136427 / 35300 : ℝ) (875 / 271979 : ℝ) (5) (1) (-2) (3379766772737 / 2500000000000 : ℝ) (3379766772739 / 2500000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hqsub_421 :
    IntervalIntegrable (fun t => Real.log ((4313 / 500 : ℝ) + (-29 / 10 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t)) volume (816519 / 511850 : ℝ) (864189 / 511850 : ℝ) ∧
      (383580807787 / 5000000000000 : ℝ) ≤ ∫ t in (816519 / 511850 : ℝ)..(864189 / 511850 : ℝ), Real.log ((4313 / 500 : ℝ) + (-29 / 10 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (816519 / 511850 : ℝ)..(864189 / 511850 : ℝ), Real.log ((4313 / 500 : ℝ) + (-29 / 10 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ≤ (767161616671 / 10000000000000 : ℝ) :=
  quad_log_div_sub (4313 / 500 : ℝ) (-29 / 10 : ℝ) (0 : ℝ) (1 : ℝ) (816519 / 511850 : ℝ) (864189 / 511850 : ℝ) (420177 / 255925 : ℝ) (4767 / 102370 : ℝ)
    (136427 / 35300 : ℝ) (420177 / 255925 : ℝ) (-102370 / 136427 : ℝ) (255925 / 420177 : ℝ) (102370 / 136427 : ℝ) (3379766772737 / 2500000000000 : ℝ) (3379766772739 / 2500000000000 : ℝ) (383580807787 / 5000000000000 : ℝ) (767161616671 / 10000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog_420 (by norm_num [quadLogLo]) (by norm_num [quadLogHi])

private lemma hqchain_422 :
    IntervalIntegrable (fun t => Real.log ((4313 / 500 : ℝ) + (-29 / 10 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t)) volume (2043 / 1450 : ℝ) (816519 / 511850 : ℝ) ∧
      (36062722207 / 200000000000 : ℝ) ≤ ∫ t in (2043 / 1450 : ℝ)..(816519 / 511850 : ℝ), Real.log ((4313 / 500 : ℝ) + (-29 / 10 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (2043 / 1450 : ℝ)..(816519 / 511850 : ℝ), Real.log ((4313 / 500 : ℝ) + (-29 / 10 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ≤ (180313611203 / 1000000000000 : ℝ) :=
  chain_int_bounds hqsub_417 hqsub_419 (by norm_num) (by norm_num)

private lemma hqchain_423 :
    IntervalIntegrable (fun t => Real.log ((4313 / 500 : ℝ) + (-29 / 10 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t)) volume (2043 / 1450 : ℝ) (864189 / 511850 : ℝ) ∧
      (642574431481 / 2500000000000 : ℝ) ≤ ∫ t in (2043 / 1450 : ℝ)..(864189 / 511850 : ℝ), Real.log ((4313 / 500 : ℝ) + (-29 / 10 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (2043 / 1450 : ℝ)..(864189 / 511850 : ℝ), Real.log ((4313 / 500 : ℝ) + (-29 / 10 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ≤ (2570297728701 / 10000000000000 : ℝ) :=
  chain_int_bounds hqchain_422 hqsub_421 (by norm_num) (by norm_num)

private lemma hqsub_424 :
    IntervalIntegrable (fun t => Real.log ((4313 / 500 : ℝ) + (-29 / 10 : ℝ) * t) / ((227 / 50 : ℝ) + (-1 : ℝ) * t)) volume (2043 / 1450 : ℝ) (768849 / 511850 : ℝ) ∧
      (44763734149 / 1000000000000 : ℝ) ≤ ∫ t in (2043 / 1450 : ℝ)..(768849 / 511850 : ℝ), Real.log ((4313 / 500 : ℝ) + (-29 / 10 : ℝ) * t) / ((227 / 50 : ℝ) + (-1 : ℝ) * t) ∧
      ∫ t in (2043 / 1450 : ℝ)..(768849 / 511850 : ℝ), Real.log ((4313 / 500 : ℝ) + (-29 / 10 : ℝ) * t) / ((227 / 50 : ℝ) + (-1 : ℝ) * t) ≤ (223818670871 / 5000000000000 : ℝ) :=
  quad_log_div_sub (4313 / 500 : ℝ) (-29 / 10 : ℝ) (227 / 50 : ℝ) (-1 : ℝ) (2043 / 1450 : ℝ) (768849 / 511850 : ℝ) (372507 / 255925 : ℝ) (4767 / 102370 : ℝ)
    (31099 / 7060 : ℝ) (315757 / 102370 : ℝ) (-20474 / 31099 : ℝ) (-102370 / 315757 : ℝ) (20474 / 31099 : ℝ) (7413653064109 / 5000000000000 : ℝ) (7413653064113 / 5000000000000 : ℝ) (44763734149 / 1000000000000 : ℝ) (223818670871 / 5000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog_416 (by norm_num [quadLogLo]) (by norm_num [quadLogHi])

private lemma hqsub_425 :
    IntervalIntegrable (fun t => Real.log ((4313 / 500 : ℝ) + (-29 / 10 : ℝ) * t) / ((227 / 50 : ℝ) + (-1 : ℝ) * t)) volume (768849 / 511850 : ℝ) (816519 / 511850 : ℝ) ∧
      (17674543849 / 400000000000 : ℝ) ≤ ∫ t in (768849 / 511850 : ℝ)..(816519 / 511850 : ℝ), Real.log ((4313 / 500 : ℝ) + (-29 / 10 : ℝ) * t) / ((227 / 50 : ℝ) + (-1 : ℝ) * t) ∧
      ∫ t in (768849 / 511850 : ℝ)..(816519 / 511850 : ℝ), Real.log ((4313 / 500 : ℝ) + (-29 / 10 : ℝ) * t) / ((227 / 50 : ℝ) + (-1 : ℝ) * t) ≤ (220931798303 / 5000000000000 : ℝ) :=
  quad_log_div_sub (4313 / 500 : ℝ) (-29 / 10 : ℝ) (227 / 50 : ℝ) (-1 : ℝ) (768849 / 511850 : ℝ) (816519 / 511850 : ℝ) (396342 / 255925 : ℝ) (4767 / 102370 : ℝ)
    (145961 / 35300 : ℝ) (306223 / 102370 : ℝ) (-102370 / 145961 : ℝ) (-102370 / 306223 : ℝ) (102370 / 145961 : ℝ) (3548641246993 / 2500000000000 : ℝ) (709728249399 / 500000000000 : ℝ) (17674543849 / 400000000000 : ℝ) (220931798303 / 5000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog_418 (by norm_num [quadLogLo]) (by norm_num [quadLogHi])

private lemma hqsub_426 :
    IntervalIntegrable (fun t => Real.log ((4313 / 500 : ℝ) + (-29 / 10 : ℝ) * t) / ((227 / 50 : ℝ) + (-1 : ℝ) * t)) volume (816519 / 511850 : ℝ) (864189 / 511850 : ℝ) ∧
      (217171211277 / 5000000000000 : ℝ) ≤ ∫ t in (816519 / 511850 : ℝ)..(864189 / 511850 : ℝ), Real.log ((4313 / 500 : ℝ) + (-29 / 10 : ℝ) * t) / ((227 / 50 : ℝ) + (-1 : ℝ) * t) ∧
      ∫ t in (816519 / 511850 : ℝ)..(864189 / 511850 : ℝ), Real.log ((4313 / 500 : ℝ) + (-29 / 10 : ℝ) * t) / ((227 / 50 : ℝ) + (-1 : ℝ) * t) ≤ (217171211571 / 5000000000000 : ℝ) :=
  quad_log_div_sub (4313 / 500 : ℝ) (-29 / 10 : ℝ) (227 / 50 : ℝ) (-1 : ℝ) (816519 / 511850 : ℝ) (864189 / 511850 : ℝ) (420177 / 255925 : ℝ) (4767 / 102370 : ℝ)
    (136427 / 35300 : ℝ) (296689 / 102370 : ℝ) (-102370 / 136427 : ℝ) (-102370 / 296689 : ℝ) (102370 / 136427 : ℝ) (3379766772737 / 2500000000000 : ℝ) (3379766772739 / 2500000000000 : ℝ) (217171211277 / 5000000000000 : ℝ) (217171211571 / 5000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog_420 (by norm_num [quadLogLo]) (by norm_num [quadLogHi])

private lemma hqchain_427 :
    IntervalIntegrable (fun t => Real.log ((4313 / 500 : ℝ) + (-29 / 10 : ℝ) * t) / ((227 / 50 : ℝ) + (-1 : ℝ) * t)) volume (2043 / 1450 : ℝ) (816519 / 511850 : ℝ) ∧
      (177900187543 / 2000000000000 : ℝ) ≤ ∫ t in (2043 / 1450 : ℝ)..(816519 / 511850 : ℝ), Real.log ((4313 / 500 : ℝ) + (-29 / 10 : ℝ) * t) / ((227 / 50 : ℝ) + (-1 : ℝ) * t) ∧
      ∫ t in (2043 / 1450 : ℝ)..(816519 / 511850 : ℝ), Real.log ((4313 / 500 : ℝ) + (-29 / 10 : ℝ) * t) / ((227 / 50 : ℝ) + (-1 : ℝ) * t) ≤ (222375234587 / 2500000000000 : ℝ) :=
  chain_int_bounds hqsub_424 hqsub_425 (by norm_num) (by norm_num)

private lemma hqchain_428 :
    IntervalIntegrable (fun t => Real.log ((4313 / 500 : ℝ) + (-29 / 10 : ℝ) * t) / ((227 / 50 : ℝ) + (-1 : ℝ) * t)) volume (2043 / 1450 : ℝ) (864189 / 511850 : ℝ) ∧
      (1323843360269 / 10000000000000 : ℝ) ≤ ∫ t in (2043 / 1450 : ℝ)..(864189 / 511850 : ℝ), Real.log ((4313 / 500 : ℝ) + (-29 / 10 : ℝ) * t) / ((227 / 50 : ℝ) + (-1 : ℝ) * t) ∧
      ∫ t in (2043 / 1450 : ℝ)..(864189 / 511850 : ℝ), Real.log ((4313 / 500 : ℝ) + (-29 / 10 : ℝ) * t) / ((227 / 50 : ℝ) + (-1 : ℝ) * t) ≤ (132384336149 / 1000000000000 : ℝ) :=
  chain_int_bounds hqchain_427 hqsub_426 (by norm_num) (by norm_num)

private lemma hact_q8_429 :
    IntervalIntegrable (fun t => Real.log ((227 / 50 : ℝ) / ((29 / 10 : ℝ) * (227 / 50 : ℝ) - (227 / 50 : ℝ) - (29 / 10 : ℝ) * t)) / (5 * t * (1 - t / (227 / 50 : ℝ)))) volume (2043 / 1450 : ℝ) (864189 / 511850 : ℝ) ∧
      (25694688251 / 5000000000000 : ℝ) ≤ ∫ t in (2043 / 1450 : ℝ)..(864189 / 511850 : ℝ), Real.log ((227 / 50 : ℝ) / ((29 / 10 : ℝ) * (227 / 50 : ℝ) - (227 / 50 : ℝ) - (29 / 10 : ℝ) * t)) / (5 * t * (1 - t / (227 / 50 : ℝ))) :=
  active_q_8 (227 / 50 : ℝ) (29 / 10 : ℝ) (4313 / 500 : ℝ) (-29 / 10 : ℝ) (2043 / 1450 : ℝ) (864189 / 511850 : ℝ) (423 / 353 : ℝ) (706 / 643 : ℝ)
    (1512927012053 / 1000000000000 : ℝ) (7564635060267 / 5000000000000 : ℝ) (904520610563 / 5000000000000 : ℝ) (1809041221133 / 10000000000000 : ℝ) (934705132553 / 10000000000000 : ℝ) (11683814157 / 125000000000 : ℝ)
    (642574431481 / 2500000000000 : ℝ) (2570297728701 / 10000000000000 : ℝ) (1323843360269 / 10000000000000 : ℝ) (132384336149 / 1000000000000 : ℝ) (25694688251 / 5000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog_373 hlog_414 hlog_415 hqchain_423 hqchain_428 (by norm_num)

private lemma hterm_413 :
    IntervalIntegrable (fun t => ind (2043 / 1450 : ℝ) (864189 / 511850 : ℝ) t / (5 * t * (1 - t / (227 / 50 : ℝ))) * Real.log ((227 / 50 : ℝ) / ((29 / 10 : ℝ) * (227 / 50 : ℝ) - (227 / 50 : ℝ) - (29 / 10 : ℝ) * t))) volume (1 : ℝ) (11 / 5 : ℝ) ∧
      (25694688251 / 5000000000000 : ℝ) ≤ ∫ t in (1 : ℝ)..(11 / 5 : ℝ), ind (2043 / 1450 : ℝ) (864189 / 511850 : ℝ) t / (5 * t * (1 - t / (227 / 50 : ℝ))) * Real.log ((227 / 50 : ℝ) / ((29 / 10 : ℝ) * (227 / 50 : ℝ) - (227 / 50 : ℝ) - (29 / 10 : ℝ) * t)) :=
  bound_ind_div_active (1 : ℝ) (11 / 5 : ℝ) (2043 / 1450 : ℝ) (864189 / 511850 : ℝ) (2043 / 1450 : ℝ) (864189 / 511850 : ℝ) (25694688251 / 5000000000000 : ℝ)
    (fun t => 5 * t * (1 - t / (227 / 50 : ℝ))) (fun t => (227 / 50 : ℝ) / ((29 / 10 : ℝ) * (227 / 50 : ℝ) - (227 / 50 : ℝ) - (29 / 10 : ℝ) * t))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (Or.inr rfl) (Or.inr rfl) hact_q8_429

private lemma hlog_431 : (2940245928297 / 5000000000000 : ℝ) ≤ Real.log (9215719 / 5118500 : ℝ) ∧ Real.log (9215719 / 5118500 : ℝ) ≤ (2940245928299 / 5000000000000 : ℝ) :=
  log_rat_bounds (9215719 / 5118500 : ℝ) (2419 / 18429019 : ℝ) (0) (2) (-1) (2940245928297 / 5000000000000 : ℝ) (2940245928299 / 5000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hqsub_432 :
    IntervalIntegrable (fun t => Real.log ((177 / 50 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t)) volume (864189 / 511850 : ℝ) (2291413 / 1279625 : ℝ) ∧
      (173051482511 / 5000000000000 : ℝ) ≤ ∫ t in (864189 / 511850 : ℝ)..(2291413 / 1279625 : ℝ), Real.log ((177 / 50 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (864189 / 511850 : ℝ)..(2291413 / 1279625 : ℝ), Real.log ((177 / 50 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ≤ (1081571767 / 31250000000 : ℝ) :=
  quad_log_div_sub (177 / 50 : ℝ) (-1 : ℝ) (0 : ℝ) (1 : ℝ) (864189 / 511850 : ℝ) (2291413 / 1279625 : ℝ) (8903771 / 5118500 : ℝ) (261881 / 5118500 : ℝ)
    (9215719 / 5118500 : ℝ) (8903771 / 5118500 : ℝ) (-5118500 / 9215719 : ℝ) (5118500 / 8903771 : ℝ) (5118500 / 8903771 : ℝ) (2940245928297 / 5000000000000 : ℝ) (2940245928299 / 5000000000000 : ℝ) (173051482511 / 5000000000000 : ℝ) (1081571767 / 31250000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog_431 (by norm_num [quadLogLo]) (by norm_num [quadLogHi])

private lemma hlog_433 : (5295366879261 / 10000000000000 : ℝ) ≤ Real.log (8691957 / 5118500 : ℝ) ∧ Real.log (8691957 / 5118500 : ℝ) ≤ (1323841719817 / 2500000000000 : ℝ) :=
  log_rat_bounds (8691957 / 5118500 : ℝ) (24217 / 7701967 : ℝ) (-4) (3) (0) (5295366879261 / 10000000000000 : ℝ) (1323841719817 / 2500000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hqsub_434 :
    IntervalIntegrable (fun t => Real.log ((177 / 50 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t)) volume (2291413 / 1279625 : ℝ) (4844707 / 2559250 : ℝ) ∧
      (294339439457 / 10000000000000 : ℝ) ≤ ∫ t in (2291413 / 1279625 : ℝ)..(4844707 / 2559250 : ℝ), Real.log ((177 / 50 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (2291413 / 1279625 : ℝ)..(4844707 / 2559250 : ℝ), Real.log ((177 / 50 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ≤ (36792429987 / 1250000000000 : ℝ) :=
  quad_log_div_sub (177 / 50 : ℝ) (-1 : ℝ) (0 : ℝ) (1 : ℝ) (2291413 / 1279625 : ℝ) (4844707 / 2559250 : ℝ) (9427533 / 5118500 : ℝ) (261881 / 5118500 : ℝ)
    (8691957 / 5118500 : ℝ) (9427533 / 5118500 : ℝ) (-5118500 / 8691957 : ℝ) (5118500 / 9427533 : ℝ) (5118500 / 8691957 : ℝ) (5295366879261 / 10000000000000 : ℝ) (1323841719817 / 2500000000000 : ℝ) (294339439457 / 10000000000000 : ℝ) (36792429987 / 1250000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog_433 (by norm_num [quadLogLo]) (by norm_num [quadLogHi])

private lemma hlog_435 : (186954610741 / 400000000000 : ℝ) ≤ Real.log (1633639 / 1023700 : ℝ) ∧ Real.log (1633639 / 1023700 : ℝ) ≤ (2336932634267 / 5000000000000 : ℝ) :=
  log_rat_bounds (1633639 / 1023700 : ℝ) (1291159 / 263358359 : ℝ) (7) (-4) (0) (186954610741 / 400000000000 : ℝ) (2336932634267 / 5000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hqsub_436 :
    IntervalIntegrable (fun t => Real.log ((177 / 50 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t)) volume (4844707 / 2559250 : ℝ) (2553294 / 1279625 : ℝ) ∧
      (6152803163 / 250000000000 : ℝ) ≤ ∫ t in (4844707 / 2559250 : ℝ)..(2553294 / 1279625 : ℝ), Real.log ((177 / 50 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (4844707 / 2559250 : ℝ)..(2553294 / 1279625 : ℝ), Real.log ((177 / 50 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ≤ (123056063553 / 5000000000000 : ℝ) :=
  quad_log_div_sub (177 / 50 : ℝ) (-1 : ℝ) (0 : ℝ) (1 : ℝ) (4844707 / 2559250 : ℝ) (2553294 / 1279625 : ℝ) (1990259 / 1023700 : ℝ) (261881 / 5118500 : ℝ)
    (1633639 / 1023700 : ℝ) (1990259 / 1023700 : ℝ) (-1023700 / 1633639 : ℝ) (1023700 / 1990259 : ℝ) (1023700 / 1633639 : ℝ) (186954610741 / 400000000000 : ℝ) (2336932634267 / 5000000000000 : ℝ) (6152803163 / 250000000000 : ℝ) (123056063553 / 5000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog_435 (by norm_num [quadLogLo]) (by norm_num [quadLogHi])

private lemma hlog_437 : (4011162431309 / 10000000000000 : ℝ) ≤ Real.log (7644433 / 5118500 : ℝ) ∧ Real.log (7644433 / 5118500 : ℝ) ≤ (1002790607829 / 2500000000000 : ℝ) :=
  log_rat_bounds (7644433 / 5118500 : ℝ) (1659691 / 411139691 : ℝ) (3) (-3) (1) (4011162431309 / 10000000000000 : ℝ) (1002790607829 / 2500000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hqsub_438 :
    IntervalIntegrable (fun t => Real.log ((177 / 50 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t)) volume (2553294 / 1279625 : ℝ) (5368469 / 2559250 : ℝ) ∧
      (5016209653 / 250000000000 : ℝ) ≤ ∫ t in (2553294 / 1279625 : ℝ)..(5368469 / 2559250 : ℝ), Real.log ((177 / 50 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (2553294 / 1279625 : ℝ)..(5368469 / 2559250 : ℝ), Real.log ((177 / 50 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ≤ (200648386937 / 10000000000000 : ℝ) :=
  quad_log_div_sub (177 / 50 : ℝ) (-1 : ℝ) (0 : ℝ) (1 : ℝ) (2553294 / 1279625 : ℝ) (5368469 / 2559250 : ℝ) (10475057 / 5118500 : ℝ) (261881 / 5118500 : ℝ)
    (7644433 / 5118500 : ℝ) (10475057 / 5118500 : ℝ) (-5118500 / 7644433 : ℝ) (5118500 / 10475057 : ℝ) (5118500 / 7644433 : ℝ) (4011162431309 / 10000000000000 : ℝ) (1002790607829 / 2500000000000 : ℝ) (5016209653 / 250000000000 : ℝ) (200648386937 / 10000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog_437 (by norm_num [quadLogLo]) (by norm_num [quadLogHi])

private lemma hlog_439 : (412675668973 / 1250000000000 : ℝ) ≤ Real.log (7120671 / 5118500 : ℝ) ∧ Real.log (7120671 / 5118500 : ℝ) ≤ (3301405351791 / 10000000000000 : ℝ) :=
  log_rat_bounds (7120671 / 5118500 : ℝ) (104789 / 128067289 : ℝ) (-1) (-2) (2) (412675668973 / 1250000000000 : ℝ) (3301405351791 / 10000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hqsub_440 :
    IntervalIntegrable (fun t => Real.log ((177 / 50 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t)) volume (5368469 / 2559250 : ℝ) (11 / 5 : ℝ) ∧
      (31454752947 / 2000000000000 : ℝ) ≤ ∫ t in (5368469 / 2559250 : ℝ)..(11 / 5 : ℝ), Real.log ((177 / 50 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (5368469 / 2559250 : ℝ)..(11 / 5 : ℝ), Real.log ((177 / 50 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ≤ (157273765919 / 10000000000000 : ℝ) :=
  quad_log_div_sub (177 / 50 : ℝ) (-1 : ℝ) (0 : ℝ) (1 : ℝ) (5368469 / 2559250 : ℝ) (11 / 5 : ℝ) (10998819 / 5118500 : ℝ) (261881 / 5118500 : ℝ)
    (7120671 / 5118500 : ℝ) (10998819 / 5118500 : ℝ) (-5118500 / 7120671 : ℝ) (5118500 / 10998819 : ℝ) (5118500 / 7120671 : ℝ) (412675668973 / 1250000000000 : ℝ) (3301405351791 / 10000000000000 : ℝ) (31454752947 / 2000000000000 : ℝ) (157273765919 / 10000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog_439 (by norm_num [quadLogLo]) (by norm_num [quadLogHi])

private lemma hqchain_441 :
    IntervalIntegrable (fun t => Real.log ((177 / 50 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t)) volume (864189 / 511850 : ℝ) (4844707 / 2559250 : ℝ) ∧
      (640442404479 / 10000000000000 : ℝ) ≤ ∫ t in (864189 / 511850 : ℝ)..(4844707 / 2559250 : ℝ), Real.log ((177 / 50 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (864189 / 511850 : ℝ)..(4844707 / 2559250 : ℝ), Real.log ((177 / 50 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ≤ (80055300667 / 1250000000000 : ℝ) :=
  chain_int_bounds hqsub_432 hqsub_434 (by norm_num) (by norm_num)

private lemma hqchain_442 :
    IntervalIntegrable (fun t => Real.log ((177 / 50 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t)) volume (864189 / 511850 : ℝ) (2553294 / 1279625 : ℝ) ∧
      (886554530999 / 10000000000000 : ℝ) ≤ ∫ t in (864189 / 511850 : ℝ)..(2553294 / 1279625 : ℝ), Real.log ((177 / 50 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (864189 / 511850 : ℝ)..(2553294 / 1279625 : ℝ), Real.log ((177 / 50 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ≤ (443277266221 / 5000000000000 : ℝ) :=
  chain_int_bounds hqchain_441 hqsub_436 (by norm_num) (by norm_num)

private lemma hqchain_443 :
    IntervalIntegrable (fun t => Real.log ((177 / 50 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t)) volume (864189 / 511850 : ℝ) (5368469 / 2559250 : ℝ) ∧
      (1087202917119 / 10000000000000 : ℝ) ≤ ∫ t in (864189 / 511850 : ℝ)..(5368469 / 2559250 : ℝ), Real.log ((177 / 50 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (864189 / 511850 : ℝ)..(5368469 / 2559250 : ℝ), Real.log ((177 / 50 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ≤ (1087202919379 / 10000000000000 : ℝ) :=
  chain_int_bounds hqchain_442 hqsub_438 (by norm_num) (by norm_num)

private lemma hqchain_444 :
    IntervalIntegrable (fun t => Real.log ((177 / 50 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t)) volume (864189 / 511850 : ℝ) (11 / 5 : ℝ) ∧
      (622238340927 / 5000000000000 : ℝ) ≤ ∫ t in (864189 / 511850 : ℝ)..(11 / 5 : ℝ), Real.log ((177 / 50 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (864189 / 511850 : ℝ)..(11 / 5 : ℝ), Real.log ((177 / 50 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ≤ (622238342649 / 5000000000000 : ℝ) :=
  chain_int_bounds hqchain_443 hqsub_440 (by norm_num) (by norm_num)

private lemma hqsub_445 :
    IntervalIntegrable (fun t => Real.log ((177 / 50 : ℝ) + (-1 : ℝ) * t) / ((227 / 50 : ℝ) + (-1 : ℝ) * t)) volume (864189 / 511850 : ℝ) (2291413 / 1279625 : ℝ) ∧
      (107390189121 / 5000000000000 : ℝ) ≤ ∫ t in (864189 / 511850 : ℝ)..(2291413 / 1279625 : ℝ), Real.log ((177 / 50 : ℝ) + (-1 : ℝ) * t) / ((227 / 50 : ℝ) + (-1 : ℝ) * t) ∧
      ∫ t in (864189 / 511850 : ℝ)..(2291413 / 1279625 : ℝ), Real.log ((177 / 50 : ℝ) + (-1 : ℝ) * t) / ((227 / 50 : ℝ) + (-1 : ℝ) * t) ≤ (214780378437 / 10000000000000 : ℝ) :=
  quad_log_div_sub (177 / 50 : ℝ) (-1 : ℝ) (227 / 50 : ℝ) (-1 : ℝ) (864189 / 511850 : ℝ) (2291413 / 1279625 : ℝ) (8903771 / 5118500 : ℝ) (261881 / 5118500 : ℝ)
    (9215719 / 5118500 : ℝ) (14334219 / 5118500 : ℝ) (-5118500 / 9215719 : ℝ) (-5118500 / 14334219 : ℝ) (5118500 / 9215719 : ℝ) (2940245928297 / 5000000000000 : ℝ) (2940245928299 / 5000000000000 : ℝ) (107390189121 / 5000000000000 : ℝ) (214780378437 / 10000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog_431 (by norm_num [quadLogLo]) (by norm_num [quadLogHi])

private lemma hqsub_446 :
    IntervalIntegrable (fun t => Real.log ((177 / 50 : ℝ) + (-1 : ℝ) * t) / ((227 / 50 : ℝ) + (-1 : ℝ) * t)) volume (2291413 / 1279625 : ℝ) (4844707 / 2559250 : ℝ) ∧
      (200721365347 / 10000000000000 : ℝ) ≤ ∫ t in (2291413 / 1279625 : ℝ)..(4844707 / 2559250 : ℝ), Real.log ((177 / 50 : ℝ) + (-1 : ℝ) * t) / ((227 / 50 : ℝ) + (-1 : ℝ) * t) ∧
      ∫ t in (2291413 / 1279625 : ℝ)..(4844707 / 2559250 : ℝ), Real.log ((177 / 50 : ℝ) + (-1 : ℝ) * t) / ((227 / 50 : ℝ) + (-1 : ℝ) * t) ≤ (200721365633 / 10000000000000 : ℝ) :=
  quad_log_div_sub (177 / 50 : ℝ) (-1 : ℝ) (227 / 50 : ℝ) (-1 : ℝ) (2291413 / 1279625 : ℝ) (4844707 / 2559250 : ℝ) (9427533 / 5118500 : ℝ) (261881 / 5118500 : ℝ)
    (8691957 / 5118500 : ℝ) (13810457 / 5118500 : ℝ) (-5118500 / 8691957 : ℝ) (-5118500 / 13810457 : ℝ) (5118500 / 8691957 : ℝ) (5295366879261 / 10000000000000 : ℝ) (1323841719817 / 2500000000000 : ℝ) (200721365347 / 10000000000000 : ℝ) (200721365633 / 10000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog_433 (by norm_num [quadLogLo]) (by norm_num [quadLogHi])

private lemma hqsub_447 :
    IntervalIntegrable (fun t => Real.log ((177 / 50 : ℝ) + (-1 : ℝ) * t) / ((227 / 50 : ℝ) + (-1 : ℝ) * t)) volume (4844707 / 2559250 : ℝ) (2553294 / 1279625 : ℝ) ∧
      (184117161077 / 10000000000000 : ℝ) ≤ ∫ t in (4844707 / 2559250 : ℝ)..(2553294 / 1279625 : ℝ), Real.log ((177 / 50 : ℝ) + (-1 : ℝ) * t) / ((227 / 50 : ℝ) + (-1 : ℝ) * t) ∧
      ∫ t in (4844707 / 2559250 : ℝ)..(2553294 / 1279625 : ℝ), Real.log ((177 / 50 : ℝ) + (-1 : ℝ) * t) / ((227 / 50 : ℝ) + (-1 : ℝ) * t) ≤ (46029290377 / 2500000000000 : ℝ) :=
  quad_log_div_sub (177 / 50 : ℝ) (-1 : ℝ) (227 / 50 : ℝ) (-1 : ℝ) (4844707 / 2559250 : ℝ) (2553294 / 1279625 : ℝ) (1990259 / 1023700 : ℝ) (261881 / 5118500 : ℝ)
    (1633639 / 1023700 : ℝ) (2657339 / 1023700 : ℝ) (-1023700 / 1633639 : ℝ) (-1023700 / 2657339 : ℝ) (1023700 / 1633639 : ℝ) (186954610741 / 400000000000 : ℝ) (2336932634267 / 5000000000000 : ℝ) (184117161077 / 10000000000000 : ℝ) (46029290377 / 2500000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog_435 (by norm_num [quadLogLo]) (by norm_num [quadLogHi])

private lemma hqsub_448 :
    IntervalIntegrable (fun t => Real.log ((177 / 50 : ℝ) + (-1 : ℝ) * t) / ((227 / 50 : ℝ) + (-1 : ℝ) * t)) volume (2553294 / 1279625 : ℝ) (5368469 / 2559250 : ℝ) ∧
      (164455650843 / 10000000000000 : ℝ) ≤ ∫ t in (2553294 / 1279625 : ℝ)..(5368469 / 2559250 : ℝ), Real.log ((177 / 50 : ℝ) + (-1 : ℝ) * t) / ((227 / 50 : ℝ) + (-1 : ℝ) * t) ∧
      ∫ t in (2553294 / 1279625 : ℝ)..(5368469 / 2559250 : ℝ), Real.log ((177 / 50 : ℝ) + (-1 : ℝ) * t) / ((227 / 50 : ℝ) + (-1 : ℝ) * t) ≤ (16445565151 / 1000000000000 : ℝ) :=
  quad_log_div_sub (177 / 50 : ℝ) (-1 : ℝ) (227 / 50 : ℝ) (-1 : ℝ) (2553294 / 1279625 : ℝ) (5368469 / 2559250 : ℝ) (10475057 / 5118500 : ℝ) (261881 / 5118500 : ℝ)
    (7644433 / 5118500 : ℝ) (12762933 / 5118500 : ℝ) (-5118500 / 7644433 : ℝ) (-5118500 / 12762933 : ℝ) (5118500 / 7644433 : ℝ) (4011162431309 / 10000000000000 : ℝ) (1002790607829 / 2500000000000 : ℝ) (164455650843 / 10000000000000 : ℝ) (16445565151 / 1000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog_437 (by norm_num [quadLogLo]) (by norm_num [quadLogHi])

private lemma hqsub_449 :
    IntervalIntegrable (fun t => Real.log ((177 / 50 : ℝ) + (-1 : ℝ) * t) / ((227 / 50 : ℝ) + (-1 : ℝ) * t)) volume (5368469 / 2559250 : ℝ) (11 / 5 : ℝ) ∧
      (28218552821 / 2000000000000 : ℝ) ≤ ∫ t in (5368469 / 2559250 : ℝ)..(11 / 5 : ℝ), Real.log ((177 / 50 : ℝ) + (-1 : ℝ) * t) / ((227 / 50 : ℝ) + (-1 : ℝ) * t) ∧
      ∫ t in (5368469 / 2559250 : ℝ)..(11 / 5 : ℝ), Real.log ((177 / 50 : ℝ) + (-1 : ℝ) * t) / ((227 / 50 : ℝ) + (-1 : ℝ) * t) ≤ (8818297823 / 625000000000 : ℝ) :=
  quad_log_div_sub (177 / 50 : ℝ) (-1 : ℝ) (227 / 50 : ℝ) (-1 : ℝ) (5368469 / 2559250 : ℝ) (11 / 5 : ℝ) (10998819 / 5118500 : ℝ) (261881 / 5118500 : ℝ)
    (7120671 / 5118500 : ℝ) (12239171 / 5118500 : ℝ) (-5118500 / 7120671 : ℝ) (-5118500 / 12239171 : ℝ) (5118500 / 7120671 : ℝ) (412675668973 / 1250000000000 : ℝ) (3301405351791 / 10000000000000 : ℝ) (28218552821 / 2000000000000 : ℝ) (8818297823 / 625000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog_439 (by norm_num [quadLogLo]) (by norm_num [quadLogHi])

private lemma hqchain_450 :
    IntervalIntegrable (fun t => Real.log ((177 / 50 : ℝ) + (-1 : ℝ) * t) / ((227 / 50 : ℝ) + (-1 : ℝ) * t)) volume (864189 / 511850 : ℝ) (4844707 / 2559250 : ℝ) ∧
      (415501743589 / 10000000000000 : ℝ) ≤ ∫ t in (864189 / 511850 : ℝ)..(4844707 / 2559250 : ℝ), Real.log ((177 / 50 : ℝ) + (-1 : ℝ) * t) / ((227 / 50 : ℝ) + (-1 : ℝ) * t) ∧
      ∫ t in (864189 / 511850 : ℝ)..(4844707 / 2559250 : ℝ), Real.log ((177 / 50 : ℝ) + (-1 : ℝ) * t) / ((227 / 50 : ℝ) + (-1 : ℝ) * t) ≤ (41550174407 / 1000000000000 : ℝ) :=
  chain_int_bounds hqsub_445 hqsub_446 (by norm_num) (by norm_num)

private lemma hqchain_451 :
    IntervalIntegrable (fun t => Real.log ((177 / 50 : ℝ) + (-1 : ℝ) * t) / ((227 / 50 : ℝ) + (-1 : ℝ) * t)) volume (864189 / 511850 : ℝ) (2553294 / 1279625 : ℝ) ∧
      (299809452333 / 5000000000000 : ℝ) ≤ ∫ t in (864189 / 511850 : ℝ)..(2553294 / 1279625 : ℝ), Real.log ((177 / 50 : ℝ) + (-1 : ℝ) * t) / ((227 / 50 : ℝ) + (-1 : ℝ) * t) ∧
      ∫ t in (864189 / 511850 : ℝ)..(2553294 / 1279625 : ℝ), Real.log ((177 / 50 : ℝ) + (-1 : ℝ) * t) / ((227 / 50 : ℝ) + (-1 : ℝ) * t) ≤ (299809452789 / 5000000000000 : ℝ) :=
  chain_int_bounds hqchain_450 hqsub_447 (by norm_num) (by norm_num)

private lemma hqchain_452 :
    IntervalIntegrable (fun t => Real.log ((177 / 50 : ℝ) + (-1 : ℝ) * t) / ((227 / 50 : ℝ) + (-1 : ℝ) * t)) volume (864189 / 511850 : ℝ) (5368469 / 2559250 : ℝ) ∧
      (764074555509 / 10000000000000 : ℝ) ≤ ∫ t in (864189 / 511850 : ℝ)..(5368469 / 2559250 : ℝ), Real.log ((177 / 50 : ℝ) + (-1 : ℝ) * t) / ((227 / 50 : ℝ) + (-1 : ℝ) * t) ∧
      ∫ t in (864189 / 511850 : ℝ)..(5368469 / 2559250 : ℝ), Real.log ((177 / 50 : ℝ) + (-1 : ℝ) * t) / ((227 / 50 : ℝ) + (-1 : ℝ) * t) ≤ (23877329909 / 312500000000 : ℝ) :=
  chain_int_bounds hqchain_451 hqsub_448 (by norm_num) (by norm_num)

private lemma hqchain_453 :
    IntervalIntegrable (fun t => Real.log ((177 / 50 : ℝ) + (-1 : ℝ) * t) / ((227 / 50 : ℝ) + (-1 : ℝ) * t)) volume (864189 / 511850 : ℝ) (11 / 5 : ℝ) ∧
      (452583659807 / 5000000000000 : ℝ) ≤ ∫ t in (864189 / 511850 : ℝ)..(11 / 5 : ℝ), Real.log ((177 / 50 : ℝ) + (-1 : ℝ) * t) / ((227 / 50 : ℝ) + (-1 : ℝ) * t) ∧
      ∫ t in (864189 / 511850 : ℝ)..(11 / 5 : ℝ), Real.log ((177 / 50 : ℝ) + (-1 : ℝ) * t) / ((227 / 50 : ℝ) + (-1 : ℝ) * t) ≤ (56572957641 / 625000000000 : ℝ) :=
  chain_int_bounds hqchain_452 hqsub_449 (by norm_num) (by norm_num)

private lemma hact_q9_454 :
    IntervalIntegrable (fun t => Real.log ((227 / 50 : ℝ) - 1 - t) / (5 * t * (1 - t / (227 / 50 : ℝ)))) volume (864189 / 511850 : ℝ) (11 / 5 : ℝ) ∧
      (429928800293 / 10000000000000 : ℝ) ≤ ∫ t in (864189 / 511850 : ℝ)..(11 / 5 : ℝ), Real.log ((227 / 50 : ℝ) - 1 - t) / (5 * t * (1 - t / (227 / 50 : ℝ))) :=
  active_q_9 (227 / 50 : ℝ) (177 / 50 : ℝ) (864189 / 511850 : ℝ) (11 / 5 : ℝ)
    (622238340927 / 5000000000000 : ℝ) (622238342649 / 5000000000000 : ℝ) (452583659807 / 5000000000000 : ℝ) (56572957641 / 625000000000 : ℝ) (429928800293 / 10000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hqchain_444 hqchain_453 (by norm_num)

private lemma hterm_430 :
    IntervalIntegrable (fun t => ind (864189 / 511850 : ℝ) (127 / 50 : ℝ) t / (5 * t * (1 - t / (227 / 50 : ℝ))) * Real.log ((227 / 50 : ℝ) - 1 - t)) volume (1 : ℝ) (11 / 5 : ℝ) ∧
      (429928800293 / 10000000000000 : ℝ) ≤ ∫ t in (1 : ℝ)..(11 / 5 : ℝ), ind (864189 / 511850 : ℝ) (127 / 50 : ℝ) t / (5 * t * (1 - t / (227 / 50 : ℝ))) * Real.log ((227 / 50 : ℝ) - 1 - t) :=
  bound_ind_div_active (1 : ℝ) (11 / 5 : ℝ) (864189 / 511850 : ℝ) (127 / 50 : ℝ) (864189 / 511850 : ℝ) (11 / 5 : ℝ) (429928800293 / 10000000000000 : ℝ)
    (fun t => 5 * t * (1 - t / (227 / 50 : ℝ))) (fun t => (227 / 50 : ℝ) - 1 - t)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (Or.inr rfl) (Or.inl rfl) hact_q9_454

private lemma hsum_455 :
    IntervalIntegrable (fun t => (sigma0 t / ((5 : ℝ) * t) * Real.log (800000000 / 22972653 : ℝ)) + (ind (127 / 50 : ℝ) (3 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) ^ (5 : ℕ) / (22972653 / 781250 : ℝ)))) volume (1 : ℝ) (11 / 5 : ℝ) ∧
      (158996267243 / 10000000000000 : ℝ) ≤ ∫ t in (1 : ℝ)..(11 / 5 : ℝ), ((sigma0 t / ((5 : ℝ) * t) * Real.log (800000000 / 22972653 : ℝ)) + (ind (127 / 50 : ℝ) (3 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) ^ (5 : ℕ) / (22972653 / 781250 : ℝ)))) :=
  add_int_lb hterm_s0_266 hterm_267 (by norm_num)

private lemma hsum_456 :
    IntervalIntegrable (fun t => ((sigma0 t / ((5 : ℝ) * t) * Real.log (800000000 / 22972653 : ℝ)) + (ind (127 / 50 : ℝ) (3 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) ^ (5 : ℕ) / (22972653 / 781250 : ℝ)))) + (ind (3807 / 2900 : ℝ) (153 / 100 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) / ((19 / 10 : ℝ) * ((253 / 100 : ℝ) - t))))) volume (1 : ℝ) (11 / 5 : ℝ) ∧
      (100476115307 / 5000000000000 : ℝ) ≤ ∫ t in (1 : ℝ)..(11 / 5 : ℝ), (((sigma0 t / ((5 : ℝ) * t) * Real.log (800000000 / 22972653 : ℝ)) + (ind (127 / 50 : ℝ) (3 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) ^ (5 : ℕ) / (22972653 / 781250 : ℝ)))) + (ind (3807 / 2900 : ℝ) (153 / 100 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) / ((19 / 10 : ℝ) * ((253 / 100 : ℝ) - t))))) :=
  add_int_lb hsum_455 hterm_268 (by norm_num)

private lemma hsum_457 :
    IntervalIntegrable (fun t => (((sigma0 t / ((5 : ℝ) * t) * Real.log (800000000 / 22972653 : ℝ)) + (ind (127 / 50 : ℝ) (3 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) ^ (5 : ℕ) / (22972653 / 781250 : ℝ)))) + (ind (3807 / 2900 : ℝ) (153 / 100 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) / ((19 / 10 : ℝ) * ((253 / 100 : ℝ) - t))))) + (ind (2561 / 1525 : ℝ) (127 / 50 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) / ((36 / 25 : ℝ) * ((177 / 50 : ℝ) - t))))) volume (1 : ℝ) (11 / 5 : ℝ) ∧
      (65603391389 / 2000000000000 : ℝ) ≤ ∫ t in (1 : ℝ)..(11 / 5 : ℝ), ((((sigma0 t / ((5 : ℝ) * t) * Real.log (800000000 / 22972653 : ℝ)) + (ind (127 / 50 : ℝ) (3 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) ^ (5 : ℕ) / (22972653 / 781250 : ℝ)))) + (ind (3807 / 2900 : ℝ) (153 / 100 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) / ((19 / 10 : ℝ) * ((253 / 100 : ℝ) - t))))) + (ind (2561 / 1525 : ℝ) (127 / 50 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) / ((36 / 25 : ℝ) * ((177 / 50 : ℝ) - t))))) :=
  add_int_lb hsum_456 hterm_282 (by norm_num)

private lemma hsum_458 :
    IntervalIntegrable (fun t => ((((sigma0 t / ((5 : ℝ) * t) * Real.log (800000000 / 22972653 : ℝ)) + (ind (127 / 50 : ℝ) (3 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) ^ (5 : ℕ) / (22972653 / 781250 : ℝ)))) + (ind (3807 / 2900 : ℝ) (153 / 100 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) / ((19 / 10 : ℝ) * ((253 / 100 : ℝ) - t))))) + (ind (2561 / 1525 : ℝ) (127 / 50 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) / ((36 / 25 : ℝ) * ((177 / 50 : ℝ) - t))))) + (ind (406 / 275 : ℝ) (127 / 50 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) / ((6 / 5 : ℝ) * ((177 / 50 : ℝ) - t))))) volume (1 : ℝ) (11 / 5 : ℝ) ∧
      (288220541373 / 5000000000000 : ℝ) ≤ ∫ t in (1 : ℝ)..(11 / 5 : ℝ), (((((sigma0 t / ((5 : ℝ) * t) * Real.log (800000000 / 22972653 : ℝ)) + (ind (127 / 50 : ℝ) (3 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) ^ (5 : ℕ) / (22972653 / 781250 : ℝ)))) + (ind (3807 / 2900 : ℝ) (153 / 100 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) / ((19 / 10 : ℝ) * ((253 / 100 : ℝ) - t))))) + (ind (2561 / 1525 : ℝ) (127 / 50 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) / ((36 / 25 : ℝ) * ((177 / 50 : ℝ) - t))))) + (ind (406 / 275 : ℝ) (127 / 50 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) / ((6 / 5 : ℝ) * ((177 / 50 : ℝ) - t))))) :=
  add_int_lb hsum_457 hterm_314 (by norm_num)

private lemma hsum_459 :
    IntervalIntegrable (fun t => (((((sigma0 t / ((5 : ℝ) * t) * Real.log (800000000 / 22972653 : ℝ)) + (ind (127 / 50 : ℝ) (3 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) ^ (5 : ℕ) / (22972653 / 781250 : ℝ)))) + (ind (3807 / 2900 : ℝ) (153 / 100 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) / ((19 / 10 : ℝ) * ((253 / 100 : ℝ) - t))))) + (ind (2561 / 1525 : ℝ) (127 / 50 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) / ((36 / 25 : ℝ) * ((177 / 50 : ℝ) - t))))) + (ind (406 / 275 : ℝ) (127 / 50 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) / ((6 / 5 : ℝ) * ((177 / 50 : ℝ) - t))))) + (ind (153 / 100 : ℝ) (127 / 50 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) ^ (2 : ℕ) / (4807 / 1000 : ℝ)))) volume (1 : ℝ) (11 / 5 : ℝ) ∧
      (951458661933 / 10000000000000 : ℝ) ≤ ∫ t in (1 : ℝ)..(11 / 5 : ℝ), ((((((sigma0 t / ((5 : ℝ) * t) * Real.log (800000000 / 22972653 : ℝ)) + (ind (127 / 50 : ℝ) (3 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) ^ (5 : ℕ) / (22972653 / 781250 : ℝ)))) + (ind (3807 / 2900 : ℝ) (153 / 100 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) / ((19 / 10 : ℝ) * ((253 / 100 : ℝ) - t))))) + (ind (2561 / 1525 : ℝ) (127 / 50 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) / ((36 / 25 : ℝ) * ((177 / 50 : ℝ) - t))))) + (ind (406 / 275 : ℝ) (127 / 50 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) / ((6 / 5 : ℝ) * ((177 / 50 : ℝ) - t))))) + (ind (153 / 100 : ℝ) (127 / 50 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) ^ (2 : ℕ) / (4807 / 1000 : ℝ)))) :=
  add_int_lb hsum_458 hterm_351 (by norm_num)

private lemma hsum_460 :
    IntervalIntegrable (fun t => ((((((sigma0 t / ((5 : ℝ) * t) * Real.log (800000000 / 22972653 : ℝ)) + (ind (127 / 50 : ℝ) (3 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) ^ (5 : ℕ) / (22972653 / 781250 : ℝ)))) + (ind (3807 / 2900 : ℝ) (153 / 100 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) / ((19 / 10 : ℝ) * ((253 / 100 : ℝ) - t))))) + (ind (2561 / 1525 : ℝ) (127 / 50 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) / ((36 / 25 : ℝ) * ((177 / 50 : ℝ) - t))))) + (ind (406 / 275 : ℝ) (127 / 50 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) / ((6 / 5 : ℝ) * ((177 / 50 : ℝ) - t))))) + (ind (153 / 100 : ℝ) (127 / 50 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) ^ (2 : ℕ) / (4807 / 1000 : ℝ)))) + (ind (750008 / 538325 : ℝ) (2561 / 1525 : ℝ) t / (5 * t * (1 - t / (227 / 50 : ℝ))) * Real.log ((227 / 50 : ℝ) ^ (2 : ℕ) / (((353 / 100 : ℝ) * (227 / 50 : ℝ) - (227 / 50 : ℝ) - (353 / 100 : ℝ) * t) * ((61 / 25 : ℝ) * (227 / 50 : ℝ) - (227 / 50 : ℝ) - (61 / 25 : ℝ) * t))))) volume (1 : ℝ) (11 / 5 : ℝ) ∧
      (132934074621 / 1250000000000 : ℝ) ≤ ∫ t in (1 : ℝ)..(11 / 5 : ℝ), (((((((sigma0 t / ((5 : ℝ) * t) * Real.log (800000000 / 22972653 : ℝ)) + (ind (127 / 50 : ℝ) (3 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) ^ (5 : ℕ) / (22972653 / 781250 : ℝ)))) + (ind (3807 / 2900 : ℝ) (153 / 100 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) / ((19 / 10 : ℝ) * ((253 / 100 : ℝ) - t))))) + (ind (2561 / 1525 : ℝ) (127 / 50 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) / ((36 / 25 : ℝ) * ((177 / 50 : ℝ) - t))))) + (ind (406 / 275 : ℝ) (127 / 50 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) / ((6 / 5 : ℝ) * ((177 / 50 : ℝ) - t))))) + (ind (153 / 100 : ℝ) (127 / 50 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) ^ (2 : ℕ) / (4807 / 1000 : ℝ)))) + (ind (750008 / 538325 : ℝ) (2561 / 1525 : ℝ) t / (5 * t * (1 - t / (227 / 50 : ℝ))) * Real.log ((227 / 50 : ℝ) ^ (2 : ℕ) / (((353 / 100 : ℝ) * (227 / 50 : ℝ) - (227 / 50 : ℝ) - (353 / 100 : ℝ) * t) * ((61 / 25 : ℝ) * (227 / 50 : ℝ) - (227 / 50 : ℝ) - (61 / 25 : ℝ) * t))))) :=
  add_int_lb hsum_459 hterm_372 (by norm_num)

private lemma hsum_461 :
    IntervalIntegrable (fun t => (((((((sigma0 t / ((5 : ℝ) * t) * Real.log (800000000 / 22972653 : ℝ)) + (ind (127 / 50 : ℝ) (3 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) ^ (5 : ℕ) / (22972653 / 781250 : ℝ)))) + (ind (3807 / 2900 : ℝ) (153 / 100 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) / ((19 / 10 : ℝ) * ((253 / 100 : ℝ) - t))))) + (ind (2561 / 1525 : ℝ) (127 / 50 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) / ((36 / 25 : ℝ) * ((177 / 50 : ℝ) - t))))) + (ind (406 / 275 : ℝ) (127 / 50 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) / ((6 / 5 : ℝ) * ((177 / 50 : ℝ) - t))))) + (ind (153 / 100 : ℝ) (127 / 50 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) ^ (2 : ℕ) / (4807 / 1000 : ℝ)))) + (ind (750008 / 538325 : ℝ) (2561 / 1525 : ℝ) t / (5 * t * (1 - t / (227 / 50 : ℝ))) * Real.log ((227 / 50 : ℝ) ^ (2 : ℕ) / (((353 / 100 : ℝ) * (227 / 50 : ℝ) - (227 / 50 : ℝ) - (353 / 100 : ℝ) * t) * ((61 / 25 : ℝ) * (227 / 50 : ℝ) - (227 / 50 : ℝ) - (61 / 25 : ℝ) * t))))) + (ind (2561 / 1525 : ℝ) (864189 / 511850 : ℝ) t / (5 * t * (1 - t / (227 / 50 : ℝ))) * Real.log ((227 / 50 : ℝ) * ((227 / 50 : ℝ) - 1 - t) / ((353 / 100 : ℝ) * (227 / 50 : ℝ) - (227 / 50 : ℝ) - (353 / 100 : ℝ) * t)))) volume (1 : ℝ) (11 / 5 : ℝ) ∧
      (13382604273 / 125000000000 : ℝ) ≤ ∫ t in (1 : ℝ)..(11 / 5 : ℝ), ((((((((sigma0 t / ((5 : ℝ) * t) * Real.log (800000000 / 22972653 : ℝ)) + (ind (127 / 50 : ℝ) (3 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) ^ (5 : ℕ) / (22972653 / 781250 : ℝ)))) + (ind (3807 / 2900 : ℝ) (153 / 100 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) / ((19 / 10 : ℝ) * ((253 / 100 : ℝ) - t))))) + (ind (2561 / 1525 : ℝ) (127 / 50 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) / ((36 / 25 : ℝ) * ((177 / 50 : ℝ) - t))))) + (ind (406 / 275 : ℝ) (127 / 50 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) / ((6 / 5 : ℝ) * ((177 / 50 : ℝ) - t))))) + (ind (153 / 100 : ℝ) (127 / 50 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) ^ (2 : ℕ) / (4807 / 1000 : ℝ)))) + (ind (750008 / 538325 : ℝ) (2561 / 1525 : ℝ) t / (5 * t * (1 - t / (227 / 50 : ℝ))) * Real.log ((227 / 50 : ℝ) ^ (2 : ℕ) / (((353 / 100 : ℝ) * (227 / 50 : ℝ) - (227 / 50 : ℝ) - (353 / 100 : ℝ) * t) * ((61 / 25 : ℝ) * (227 / 50 : ℝ) - (227 / 50 : ℝ) - (61 / 25 : ℝ) * t))))) + (ind (2561 / 1525 : ℝ) (864189 / 511850 : ℝ) t / (5 * t * (1 - t / (227 / 50 : ℝ))) * Real.log ((227 / 50 : ℝ) * ((227 / 50 : ℝ) - 1 - t) / ((353 / 100 : ℝ) * (227 / 50 : ℝ) - (227 / 50 : ℝ) - (353 / 100 : ℝ) * t)))) :=
  add_int_lb hsum_460 hterm_403 (by norm_num)

private lemma hsum_462 :
    IntervalIntegrable (fun t => ((((((((sigma0 t / ((5 : ℝ) * t) * Real.log (800000000 / 22972653 : ℝ)) + (ind (127 / 50 : ℝ) (3 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) ^ (5 : ℕ) / (22972653 / 781250 : ℝ)))) + (ind (3807 / 2900 : ℝ) (153 / 100 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) / ((19 / 10 : ℝ) * ((253 / 100 : ℝ) - t))))) + (ind (2561 / 1525 : ℝ) (127 / 50 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) / ((36 / 25 : ℝ) * ((177 / 50 : ℝ) - t))))) + (ind (406 / 275 : ℝ) (127 / 50 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) / ((6 / 5 : ℝ) * ((177 / 50 : ℝ) - t))))) + (ind (153 / 100 : ℝ) (127 / 50 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) ^ (2 : ℕ) / (4807 / 1000 : ℝ)))) + (ind (750008 / 538325 : ℝ) (2561 / 1525 : ℝ) t / (5 * t * (1 - t / (227 / 50 : ℝ))) * Real.log ((227 / 50 : ℝ) ^ (2 : ℕ) / (((353 / 100 : ℝ) * (227 / 50 : ℝ) - (227 / 50 : ℝ) - (353 / 100 : ℝ) * t) * ((61 / 25 : ℝ) * (227 / 50 : ℝ) - (227 / 50 : ℝ) - (61 / 25 : ℝ) * t))))) + (ind (2561 / 1525 : ℝ) (864189 / 511850 : ℝ) t / (5 * t * (1 - t / (227 / 50 : ℝ))) * Real.log ((227 / 50 : ℝ) * ((227 / 50 : ℝ) - 1 - t) / ((353 / 100 : ℝ) * (227 / 50 : ℝ) - (227 / 50 : ℝ) - (353 / 100 : ℝ) * t)))) + (ind (2043 / 1450 : ℝ) (864189 / 511850 : ℝ) t / (5 * t * (1 - t / (227 / 50 : ℝ))) * Real.log ((227 / 50 : ℝ) / ((29 / 10 : ℝ) * (227 / 50 : ℝ) - (227 / 50 : ℝ) - (29 / 10 : ℝ) * t)))) volume (1 : ℝ) (11 / 5 : ℝ) ∧
      (560998859171 / 5000000000000 : ℝ) ≤ ∫ t in (1 : ℝ)..(11 / 5 : ℝ), (((((((((sigma0 t / ((5 : ℝ) * t) * Real.log (800000000 / 22972653 : ℝ)) + (ind (127 / 50 : ℝ) (3 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) ^ (5 : ℕ) / (22972653 / 781250 : ℝ)))) + (ind (3807 / 2900 : ℝ) (153 / 100 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) / ((19 / 10 : ℝ) * ((253 / 100 : ℝ) - t))))) + (ind (2561 / 1525 : ℝ) (127 / 50 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) / ((36 / 25 : ℝ) * ((177 / 50 : ℝ) - t))))) + (ind (406 / 275 : ℝ) (127 / 50 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) / ((6 / 5 : ℝ) * ((177 / 50 : ℝ) - t))))) + (ind (153 / 100 : ℝ) (127 / 50 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) ^ (2 : ℕ) / (4807 / 1000 : ℝ)))) + (ind (750008 / 538325 : ℝ) (2561 / 1525 : ℝ) t / (5 * t * (1 - t / (227 / 50 : ℝ))) * Real.log ((227 / 50 : ℝ) ^ (2 : ℕ) / (((353 / 100 : ℝ) * (227 / 50 : ℝ) - (227 / 50 : ℝ) - (353 / 100 : ℝ) * t) * ((61 / 25 : ℝ) * (227 / 50 : ℝ) - (227 / 50 : ℝ) - (61 / 25 : ℝ) * t))))) + (ind (2561 / 1525 : ℝ) (864189 / 511850 : ℝ) t / (5 * t * (1 - t / (227 / 50 : ℝ))) * Real.log ((227 / 50 : ℝ) * ((227 / 50 : ℝ) - 1 - t) / ((353 / 100 : ℝ) * (227 / 50 : ℝ) - (227 / 50 : ℝ) - (353 / 100 : ℝ) * t)))) + (ind (2043 / 1450 : ℝ) (864189 / 511850 : ℝ) t / (5 * t * (1 - t / (227 / 50 : ℝ))) * Real.log ((227 / 50 : ℝ) / ((29 / 10 : ℝ) * (227 / 50 : ℝ) - (227 / 50 : ℝ) - (29 / 10 : ℝ) * t)))) :=
  add_int_lb hsum_461 hterm_413 (by norm_num)

private lemma hsum_463 :
    IntervalIntegrable (fun t => (((((((((sigma0 t / ((5 : ℝ) * t) * Real.log (800000000 / 22972653 : ℝ)) + (ind (127 / 50 : ℝ) (3 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) ^ (5 : ℕ) / (22972653 / 781250 : ℝ)))) + (ind (3807 / 2900 : ℝ) (153 / 100 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) / ((19 / 10 : ℝ) * ((253 / 100 : ℝ) - t))))) + (ind (2561 / 1525 : ℝ) (127 / 50 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) / ((36 / 25 : ℝ) * ((177 / 50 : ℝ) - t))))) + (ind (406 / 275 : ℝ) (127 / 50 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) / ((6 / 5 : ℝ) * ((177 / 50 : ℝ) - t))))) + (ind (153 / 100 : ℝ) (127 / 50 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) ^ (2 : ℕ) / (4807 / 1000 : ℝ)))) + (ind (750008 / 538325 : ℝ) (2561 / 1525 : ℝ) t / (5 * t * (1 - t / (227 / 50 : ℝ))) * Real.log ((227 / 50 : ℝ) ^ (2 : ℕ) / (((353 / 100 : ℝ) * (227 / 50 : ℝ) - (227 / 50 : ℝ) - (353 / 100 : ℝ) * t) * ((61 / 25 : ℝ) * (227 / 50 : ℝ) - (227 / 50 : ℝ) - (61 / 25 : ℝ) * t))))) + (ind (2561 / 1525 : ℝ) (864189 / 511850 : ℝ) t / (5 * t * (1 - t / (227 / 50 : ℝ))) * Real.log ((227 / 50 : ℝ) * ((227 / 50 : ℝ) - 1 - t) / ((353 / 100 : ℝ) * (227 / 50 : ℝ) - (227 / 50 : ℝ) - (353 / 100 : ℝ) * t)))) + (ind (2043 / 1450 : ℝ) (864189 / 511850 : ℝ) t / (5 * t * (1 - t / (227 / 50 : ℝ))) * Real.log ((227 / 50 : ℝ) / ((29 / 10 : ℝ) * (227 / 50 : ℝ) - (227 / 50 : ℝ) - (29 / 10 : ℝ) * t)))) + (ind (864189 / 511850 : ℝ) (127 / 50 : ℝ) t / (5 * t * (1 - t / (227 / 50 : ℝ))) * Real.log ((227 / 50 : ℝ) - 1 - t))) volume (1 : ℝ) (11 / 5 : ℝ) ∧
      (310385303727 / 2000000000000 : ℝ) ≤ ∫ t in (1 : ℝ)..(11 / 5 : ℝ), ((((((((((sigma0 t / ((5 : ℝ) * t) * Real.log (800000000 / 22972653 : ℝ)) + (ind (127 / 50 : ℝ) (3 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) ^ (5 : ℕ) / (22972653 / 781250 : ℝ)))) + (ind (3807 / 2900 : ℝ) (153 / 100 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) / ((19 / 10 : ℝ) * ((253 / 100 : ℝ) - t))))) + (ind (2561 / 1525 : ℝ) (127 / 50 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) / ((36 / 25 : ℝ) * ((177 / 50 : ℝ) - t))))) + (ind (406 / 275 : ℝ) (127 / 50 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) / ((6 / 5 : ℝ) * ((177 / 50 : ℝ) - t))))) + (ind (153 / 100 : ℝ) (127 / 50 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) ^ (2 : ℕ) / (4807 / 1000 : ℝ)))) + (ind (750008 / 538325 : ℝ) (2561 / 1525 : ℝ) t / (5 * t * (1 - t / (227 / 50 : ℝ))) * Real.log ((227 / 50 : ℝ) ^ (2 : ℕ) / (((353 / 100 : ℝ) * (227 / 50 : ℝ) - (227 / 50 : ℝ) - (353 / 100 : ℝ) * t) * ((61 / 25 : ℝ) * (227 / 50 : ℝ) - (227 / 50 : ℝ) - (61 / 25 : ℝ) * t))))) + (ind (2561 / 1525 : ℝ) (864189 / 511850 : ℝ) t / (5 * t * (1 - t / (227 / 50 : ℝ))) * Real.log ((227 / 50 : ℝ) * ((227 / 50 : ℝ) - 1 - t) / ((353 / 100 : ℝ) * (227 / 50 : ℝ) - (227 / 50 : ℝ) - (353 / 100 : ℝ) * t)))) + (ind (2043 / 1450 : ℝ) (864189 / 511850 : ℝ) t / (5 * t * (1 - t / (227 / 50 : ℝ))) * Real.log ((227 / 50 : ℝ) / ((29 / 10 : ℝ) * (227 / 50 : ℝ) - (227 / 50 : ℝ) - (29 / 10 : ℝ) * t)))) + (ind (864189 / 511850 : ℝ) (127 / 50 : ℝ) t / (5 * t * (1 - t / (227 / 50 : ℝ))) * Real.log ((227 / 50 : ℝ) - 1 - t))) :=
  add_int_lb hsum_462 hterm_430 (by norm_num)


private lemma hkern_eq (t : ℝ) : tableKernel 0 t = ((((((((((sigma0 t / ((5 : ℝ) * t) * Real.log (800000000 / 22972653 : ℝ)) + (ind (127 / 50 : ℝ) (3 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) ^ (5 : ℕ) / (22972653 / 781250 : ℝ)))) + (ind (3807 / 2900 : ℝ) (153 / 100 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) / ((19 / 10 : ℝ) * ((253 / 100 : ℝ) - t))))) + (ind (2561 / 1525 : ℝ) (127 / 50 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) / ((36 / 25 : ℝ) * ((177 / 50 : ℝ) - t))))) + (ind (406 / 275 : ℝ) (127 / 50 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) / ((6 / 5 : ℝ) * ((177 / 50 : ℝ) - t))))) + (ind (153 / 100 : ℝ) (127 / 50 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) ^ (2 : ℕ) / (4807 / 1000 : ℝ)))) + (ind (750008 / 538325 : ℝ) (2561 / 1525 : ℝ) t / (5 * t * (1 - t / (227 / 50 : ℝ))) * Real.log ((227 / 50 : ℝ) ^ (2 : ℕ) / (((353 / 100 : ℝ) * (227 / 50 : ℝ) - (227 / 50 : ℝ) - (353 / 100 : ℝ) * t) * ((61 / 25 : ℝ) * (227 / 50 : ℝ) - (227 / 50 : ℝ) - (61 / 25 : ℝ) * t))))) + (ind (2561 / 1525 : ℝ) (864189 / 511850 : ℝ) t / (5 * t * (1 - t / (227 / 50 : ℝ))) * Real.log ((227 / 50 : ℝ) * ((227 / 50 : ℝ) - 1 - t) / ((353 / 100 : ℝ) * (227 / 50 : ℝ) - (227 / 50 : ℝ) - (353 / 100 : ℝ) * t)))) + (ind (2043 / 1450 : ℝ) (864189 / 511850 : ℝ) t / (5 * t * (1 - t / (227 / 50 : ℝ))) * Real.log ((227 / 50 : ℝ) / ((29 / 10 : ℝ) * (227 / 50 : ℝ) - (227 / 50 : ℝ) - (29 / 10 : ℝ) * t)))) + (ind (864189 / 511850 : ℝ) (127 / 50 : ℝ) t / (5 * t * (1 - t / (227 / 50 : ℝ))) * Real.log ((227 / 50 : ℝ) - 1 - t))) := by
  have hs : (tableParams ⟨(0 : Fin 9).val, by omega⟩).s = (11 / 5 : ℝ) := by simp [tableParams]; try norm_num
  have hsp : (tableParams ⟨(0 : Fin 9).val, by omega⟩).sp = (227 / 50 : ℝ) := by simp [tableParams]; try norm_num
  have hk1 : (tableParams ⟨(0 : Fin 9).val, by omega⟩).k1 = (353 / 100 : ℝ) := by simp [tableParams]; try norm_num
  have hk2 : (tableParams ⟨(0 : Fin 9).val, by omega⟩).k2 = (29 / 10 : ℝ) := by simp [tableParams]; try norm_num
  have hk3 : (tableParams ⟨(0 : Fin 9).val, by omega⟩).k3 = (61 / 25 : ℝ) := by simp [tableParams]; try norm_num
  have ha0 : alpha (tableParams ⟨(0 : Fin 9).val, by omega⟩) 0 = (153 / 100 : ℝ) := by simp [alpha, tableParams]; try norm_num
  have ha1 : alpha (tableParams ⟨(0 : Fin 9).val, by omega⟩) 1 = (127 / 50 : ℝ) := by simp [alpha, tableParams]; try norm_num
  have ha2 : alpha (tableParams ⟨(0 : Fin 9).val, by omega⟩) 2 = (406 / 275 : ℝ) := by simp [alpha, tableParams]; try norm_num
  have ha4 : alpha (tableParams ⟨(0 : Fin 9).val, by omega⟩) 4 = (2561 / 1525 : ℝ) := by simp [alpha, tableParams]; try norm_num
  have ha5 : alpha (tableParams ⟨(0 : Fin 9).val, by omega⟩) 5 = (2043 / 1450 : ℝ) := by simp [alpha, tableParams]; try norm_num
  have ha6 : alpha (tableParams ⟨(0 : Fin 9).val, by omega⟩) 6 = (750008 / 538325 : ℝ) := by simp [alpha, tableParams]; try norm_num
  have ha7 : alpha (tableParams ⟨(0 : Fin 9).val, by omega⟩) 7 = (864189 / 511850 : ℝ) := by simp [alpha, tableParams]; try norm_num
  have ha8 : alpha (tableParams ⟨(0 : Fin 9).val, by omega⟩) 8 = (3807 / 2900 : ℝ) := by simp [alpha, tableParams]; try norm_num
  unfold tableKernel
  rw [dif_pos (by decide)]
  unfold Xi2
  dsimp only
  rw [ha0, ha1, ha2, ha4, ha5, ha6, ha7, ha8, hs, hsp, hk1, hk2, hk3]
  rw [(show (1024 : ℝ) / (((11 / 5 : ℝ) - 1) * ((227 / 50 : ℝ) - 1) * ((353 / 100 : ℝ) - 1) * ((29 / 10 : ℝ) - 1) * ((61 / 25 : ℝ) - 1)) = (800000000 / 22972653 : ℝ) by norm_num),
      (show ((11 / 5 : ℝ) - 1) * ((227 / 50 : ℝ) - 1) * ((353 / 100 : ℝ) - 1) * ((29 / 10 : ℝ) - 1) * ((61 / 25 : ℝ) - 1) = (22972653 / 781250 : ℝ) by norm_num),
      (show ((353 / 100 : ℝ) - 1) * ((29 / 10 : ℝ) - 1) = (4807 / 1000 : ℝ) by norm_num),
      (show (29 / 10 : ℝ) - 1 = (19 / 10 : ℝ) by norm_num),
      (show (353 / 100 : ℝ) - 1 = (253 / 100 : ℝ) by norm_num),
      (show (61 / 25 : ℝ) - 1 = (36 / 25 : ℝ) by norm_num),
      (show (227 / 50 : ℝ) - 1 = (177 / 50 : ℝ) by norm_num),
      (show (11 / 5 : ℝ) - 1 = (6 / 5 : ℝ) by norm_num)]



theorem main_thm : (candidateMatrixQ 0 0 : ℝ) ≤ integralMatrix 0 0 := by
  have hcand : (candidateMatrixQ 0 0 : ℝ) = (775963 / 5000000 : ℝ) := by simp [candidateMatrixQ]; try norm_num
  have hga : grid ⟨(0 : Fin 9).val, by omega⟩ = (1 : ℝ) := by simp [grid]; try norm_num
  have hgb : grid ⟨(0 : Fin 9).val + 1, by omega⟩ = (11 / 5 : ℝ) := by simp [grid]; try norm_num
  unfold integralMatrix
  rw [hcand, hga, hgb]
  have hint_eq : (∫ t in (1 : ℝ)..(11 / 5 : ℝ), tableKernel 0 t) =
      ∫ t in (1 : ℝ)..(11 / 5 : ℝ), ((((((((((sigma0 t / ((5 : ℝ) * t) * Real.log (800000000 / 22972653 : ℝ)) + (ind (127 / 50 : ℝ) (3 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) ^ (5 : ℕ) / (22972653 / 781250 : ℝ)))) + (ind (3807 / 2900 : ℝ) (153 / 100 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) / ((19 / 10 : ℝ) * ((253 / 100 : ℝ) - t))))) + (ind (2561 / 1525 : ℝ) (127 / 50 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) / ((36 / 25 : ℝ) * ((177 / 50 : ℝ) - t))))) + (ind (406 / 275 : ℝ) (127 / 50 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) / ((6 / 5 : ℝ) * ((177 / 50 : ℝ) - t))))) + (ind (153 / 100 : ℝ) (127 / 50 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) ^ (2 : ℕ) / (4807 / 1000 : ℝ)))) + (ind (750008 / 538325 : ℝ) (2561 / 1525 : ℝ) t / (5 * t * (1 - t / (227 / 50 : ℝ))) * Real.log ((227 / 50 : ℝ) ^ (2 : ℕ) / (((353 / 100 : ℝ) * (227 / 50 : ℝ) - (227 / 50 : ℝ) - (353 / 100 : ℝ) * t) * ((61 / 25 : ℝ) * (227 / 50 : ℝ) - (227 / 50 : ℝ) - (61 / 25 : ℝ) * t))))) + (ind (2561 / 1525 : ℝ) (864189 / 511850 : ℝ) t / (5 * t * (1 - t / (227 / 50 : ℝ))) * Real.log ((227 / 50 : ℝ) * ((227 / 50 : ℝ) - 1 - t) / ((353 / 100 : ℝ) * (227 / 50 : ℝ) - (227 / 50 : ℝ) - (353 / 100 : ℝ) * t)))) + (ind (2043 / 1450 : ℝ) (864189 / 511850 : ℝ) t / (5 * t * (1 - t / (227 / 50 : ℝ))) * Real.log ((227 / 50 : ℝ) / ((29 / 10 : ℝ) * (227 / 50 : ℝ) - (227 / 50 : ℝ) - (29 / 10 : ℝ) * t)))) + (ind (864189 / 511850 : ℝ) (127 / 50 : ℝ) t / (5 * t * (1 - t / (227 / 50 : ℝ))) * Real.log ((227 / 50 : ℝ) - 1 - t))) := by
    apply integral_congr; intro t _; exact hkern_eq t
  rw [hint_eq]
  exact le_trans (by norm_num) hsum_463.2

end
end W5Cert_R1_entry_0_0

theorem solution : (candidateMatrixQ 0 0 : ℝ) ≤ integralMatrix 0 0 :=
  W5Cert_R1_entry_0_0.main_thm
