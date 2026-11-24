-- Prove2me | solution 1 for LL_Burst9MatrixR1.entry_0_2
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-24T00:59:32.86086+00:00
-- url     : https://prove2.me/submissions/e0eb2852-2c05-4509-b5ab-6def53ff529b

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

namespace W5Cert_R1_entry_0_2
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

private lemma hlog_49 : (97527473119 / 5000000000000 : ℝ) ≤ Real.log (673 / 660 : ℝ) ∧ Real.log (673 / 660 : ℝ) ≤ (195054946247 / 10000000000000 : ℝ) :=
  log_rat_bounds (673 / 660 : ℝ) (19 / 5365 : ℝ) (-4) (4) (-1) (97527473119 / 5000000000000 : ℝ) (195054946247 / 10000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hqsub_50 :
    IntervalIntegrable (fun t => Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t)) volume (1 : ℝ) (123 / 110 : ℝ) ∧
      (2764113113 / 2500000000000 : ℝ) ≤ ∫ t in (1 : ℝ)..(123 / 110 : ℝ), Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (1 : ℝ)..(123 / 110 : ℝ), Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t) ≤ (442258111 / 400000000000 : ℝ) :=
  quad_log_div_sub (2 / 3 : ℝ) (1 / 3 : ℝ) (1 : ℝ) (1 : ℝ) (1 : ℝ) (123 / 110 : ℝ) (233 / 220 : ℝ) (13 / 220 : ℝ)
    (673 / 660 : ℝ) (453 / 220 : ℝ) (220 / 673 : ℝ) (220 / 453 : ℝ) (220 / 453 : ℝ) (97527473119 / 5000000000000 : ℝ) (195054946247 / 10000000000000 : ℝ) (2764113113 / 2500000000000 : ℝ) (442258111 / 400000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog_49 (by norm_num [quadLogLo]) (by norm_num [quadLogHi])

private lemma hlog_51 : (574109072129 / 10000000000000 : ℝ) ≤ Real.log (233 / 220 : ℝ) ∧ Real.log (233 / 220 : ℝ) ≤ (287054536069 / 5000000000000 : ℝ) :=
  log_rat_bounds (233 / 220 : ℝ) (31 / 14881 : ℝ) (-7) (3) (1) (574109072129 / 10000000000000 : ℝ) (287054536069 / 5000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hqsub_52 :
    IntervalIntegrable (fun t => Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t)) volume (123 / 110 : ℝ) (68 / 55 : ℝ) ∧
      (388093389 / 125000000000 : ℝ) ≤ ∫ t in (123 / 110 : ℝ)..(68 / 55 : ℝ), Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (123 / 110 : ℝ)..(68 / 55 : ℝ), Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t) ≤ (1552373567 / 500000000000 : ℝ) :=
  quad_log_div_sub (2 / 3 : ℝ) (1 / 3 : ℝ) (1 : ℝ) (1 : ℝ) (123 / 110 : ℝ) (68 / 55 : ℝ) (259 / 220 : ℝ) (13 / 220 : ℝ)
    (233 / 220 : ℝ) (479 / 220 : ℝ) (220 / 699 : ℝ) (220 / 479 : ℝ) (220 / 479 : ℝ) (574109072129 / 10000000000000 : ℝ) (287054536069 / 5000000000000 : ℝ) (388093389 / 125000000000 : ℝ) (1552373567 / 500000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog_51 (by norm_num [quadLogLo]) (by norm_num [quadLogHi])

private lemma hlog_53 : (939318198339 / 10000000000000 : ℝ) ≤ Real.log (145 / 132 : ℝ) ∧ Real.log (145 / 132 : ℝ) ≤ (187863639669 / 2000000000000 : ℝ) :=
  log_rat_bounds (145 / 132 : ℝ) (61 / 7189 : ℝ) (0) (3) (-2) (939318198339 / 10000000000000 : ℝ) (187863639669 / 2000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hqsub_54 :
    IntervalIntegrable (fun t => Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t)) volume (68 / 55 : ℝ) (149 / 110 : ℝ) ∧
      (48264767223 / 10000000000000 : ℝ) ≤ ∫ t in (68 / 55 : ℝ)..(149 / 110 : ℝ), Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (68 / 55 : ℝ)..(149 / 110 : ℝ), Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t) ≤ (48264767377 / 10000000000000 : ℝ) :=
  quad_log_div_sub (2 / 3 : ℝ) (1 / 3 : ℝ) (1 : ℝ) (1 : ℝ) (68 / 55 : ℝ) (149 / 110 : ℝ) (57 / 44 : ℝ) (13 / 220 : ℝ)
    (145 / 132 : ℝ) (101 / 44 : ℝ) (44 / 145 : ℝ) (44 / 101 : ℝ) (44 / 101 : ℝ) (939318198339 / 10000000000000 : ℝ) (187863639669 / 2000000000000 : ℝ) (48264767223 / 10000000000000 : ℝ) (48264767377 / 10000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog_53 (by norm_num [quadLogLo]) (by norm_num [quadLogHi])

private lemma hlog_55 : (645829083717 / 5000000000000 : ℝ) ≤ Real.log (751 / 660 : ℝ) ∧ Real.log (751 / 660 : ℝ) ≤ (1291658167439 / 10000000000000 : ℝ) :=
  log_rat_bounds (751 / 660 : ℝ) (17 / 2987 : ℝ) (-3) (2) (0) (645829083717 / 5000000000000 : ℝ) (1291658167439 / 10000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hqsub_56 :
    IntervalIntegrable (fun t => Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t)) volume (149 / 110 : ℝ) (81 / 55 : ℝ) ∧
      (31582005551 / 5000000000000 : ℝ) ≤ ∫ t in (149 / 110 : ℝ)..(81 / 55 : ℝ), Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (149 / 110 : ℝ)..(81 / 55 : ℝ), Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t) ≤ (63164011211 / 10000000000000 : ℝ) :=
  quad_log_div_sub (2 / 3 : ℝ) (1 / 3 : ℝ) (1 : ℝ) (1 : ℝ) (149 / 110 : ℝ) (81 / 55 : ℝ) (311 / 220 : ℝ) (13 / 220 : ℝ)
    (751 / 660 : ℝ) (531 / 220 : ℝ) (220 / 751 : ℝ) (220 / 531 : ℝ) (220 / 531 : ℝ) (645829083717 / 5000000000000 : ℝ) (1291658167439 / 10000000000000 : ℝ) (31582005551 / 5000000000000 : ℝ) (63164011211 / 10000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog_55 (by norm_num [quadLogLo]) (by norm_num [quadLogHi])

private lemma hlog_57 : (1632005153467 / 10000000000000 : ℝ) ≤ Real.log (259 / 220 : ℝ) ∧ Real.log (259 / 220 : ℝ) ≤ (408001288369 / 2500000000000 : ℝ) :=
  log_rat_bounds (259 / 220 : ℝ) (19 / 8269 : ℝ) (-6) (1) (2) (1632005153467 / 10000000000000 : ℝ) (408001288369 / 2500000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hqsub_58 :
    IntervalIntegrable (fun t => Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t)) volume (81 / 55 : ℝ) (35 / 22 : ℝ) ∧
      (19027760533 / 2500000000000 : ℝ) ≤ ∫ t in (81 / 55 : ℝ)..(35 / 22 : ℝ), Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (81 / 55 : ℝ)..(35 / 22 : ℝ), Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t) ≤ (7611104221 / 1000000000000 : ℝ) :=
  quad_log_div_sub (2 / 3 : ℝ) (1 / 3 : ℝ) (1 : ℝ) (1 : ℝ) (81 / 55 : ℝ) (35 / 22 : ℝ) (337 / 220 : ℝ) (13 / 220 : ℝ)
    (259 / 220 : ℝ) (557 / 220 : ℝ) (220 / 777 : ℝ) (220 / 557 : ℝ) (220 / 557 : ℝ) (1632005153467 / 10000000000000 : ℝ) (408001288369 / 2500000000000 : ℝ) (19027760533 / 2500000000000 : ℝ) (7611104221 / 1000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog_57 (by norm_num [quadLogLo]) (by norm_num [quadLogHi])

private lemma hlog_59 : (1961148789261 / 10000000000000 : ℝ) ≤ Real.log (73 / 60 : ℝ) ∧ Real.log (73 / 60 : ℝ) ≤ (392229757853 / 2000000000000 : ℝ) :=
  log_rat_bounds (73 / 60 : ℝ) (1 / 145 : ℝ) (1) (1) (-1) (1961148789261 / 10000000000000 : ℝ) (392229757853 / 2000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hqsub_60 :
    IntervalIntegrable (fun t => Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t)) volume (35 / 22 : ℝ) (94 / 55 : ℝ) ∧
      (87402509687 / 10000000000000 : ℝ) ≤ ∫ t in (35 / 22 : ℝ)..(94 / 55 : ℝ), Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (35 / 22 : ℝ)..(94 / 55 : ℝ), Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t) ≤ (5462656859 / 625000000000 : ℝ) :=
  quad_log_div_sub (2 / 3 : ℝ) (1 / 3 : ℝ) (1 : ℝ) (1 : ℝ) (35 / 22 : ℝ) (94 / 55 : ℝ) (33 / 20 : ℝ) (13 / 220 : ℝ)
    (73 / 60 : ℝ) (53 / 20 : ℝ) (20 / 73 : ℝ) (20 / 53 : ℝ) (20 / 53 : ℝ) (1961148789261 / 10000000000000 : ℝ) (392229757853 / 2000000000000 : ℝ) (87402509687 / 10000000000000 : ℝ) (5462656859 / 625000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog_59 (by norm_num [quadLogLo]) (by norm_num [quadLogHi])

private lemma hlog_61 : (1139901600573 / 5000000000000 : ℝ) ≤ Real.log (829 / 660 : ℝ) ∧ Real.log (829 / 660 : ℝ) ≤ (45596064023 / 200000000000 : ℝ) :=
  log_rat_bounds (829 / 660 : ℝ) (2 / 827 : ℝ) (-2) (0) (1) (1139901600573 / 5000000000000 : ℝ) (45596064023 / 200000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hqsub_62 :
    IntervalIntegrable (fun t => Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t)) volume (94 / 55 : ℝ) (201 / 110 : ℝ) ∧
      (12160141317 / 1250000000000 : ℝ) ≤ ∫ t in (94 / 55 : ℝ)..(201 / 110 : ℝ), Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (94 / 55 : ℝ)..(201 / 110 : ℝ), Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t) ≤ (97281130579 / 10000000000000 : ℝ) :=
  quad_log_div_sub (2 / 3 : ℝ) (1 / 3 : ℝ) (1 : ℝ) (1 : ℝ) (94 / 55 : ℝ) (201 / 110 : ℝ) (389 / 220 : ℝ) (13 / 220 : ℝ)
    (829 / 660 : ℝ) (609 / 220 : ℝ) (220 / 829 : ℝ) (220 / 609 : ℝ) (220 / 609 : ℝ) (1139901600573 / 5000000000000 : ℝ) (45596064023 / 200000000000 : ℝ) (12160141317 / 1250000000000 : ℝ) (97281130579 / 10000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog_61 (by norm_num [quadLogLo]) (by norm_num [quadLogHi])

private lemma hlog_63 : (2588616339159 / 10000000000000 : ℝ) ≤ Real.log (57 / 44 : ℝ) ∧ Real.log (57 / 44 : ℝ) ≤ (1294308169583 / 5000000000000 : ℝ) :=
  log_rat_bounds (57 / 44 : ℝ) (17 / 2833 : ℝ) (5) (0) (-2) (2588616339159 / 10000000000000 : ℝ) (1294308169583 / 5000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hqsub_64 :
    IntervalIntegrable (fun t => Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t)) volume (201 / 110 : ℝ) (107 / 55 : ℝ) ∧
      (52973561843 / 5000000000000 : ℝ) ≤ ∫ t in (201 / 110 : ℝ)..(107 / 55 : ℝ), Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (201 / 110 : ℝ)..(107 / 55 : ℝ), Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t) ≤ (52973561859 / 5000000000000 : ℝ) :=
  quad_log_div_sub (2 / 3 : ℝ) (1 / 3 : ℝ) (1 : ℝ) (1 : ℝ) (201 / 110 : ℝ) (107 / 55 : ℝ) (83 / 44 : ℝ) (13 / 220 : ℝ)
    (57 / 44 : ℝ) (127 / 44 : ℝ) (44 / 171 : ℝ) (44 / 127 : ℝ) (44 / 127 : ℝ) (2588616339159 / 10000000000000 : ℝ) (1294308169583 / 5000000000000 : ℝ) (52973561843 / 5000000000000 : ℝ) (52973561859 / 5000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog_63 (by norm_num [quadLogLo]) (by norm_num [quadLogHi])

private lemma hlog_65 : (577635581831 / 2000000000000 : ℝ) ≤ Real.log (881 / 660 : ℝ) ∧ Real.log (881 / 660 : ℝ) ≤ (2888177909159 / 10000000000000 : ℝ) :=
  log_rat_bounds (881 / 660 : ℝ) (1 / 1761 : ℝ) (2) (-1) (0) (577635581831 / 2000000000000 : ℝ) (2888177909159 / 10000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hqsub_66 :
    IntervalIntegrable (fun t => Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t)) volume (107 / 55 : ℝ) (227 / 110 : ℝ) ∧
      (113566888557 / 10000000000000 : ℝ) ≤ ∫ t in (107 / 55 : ℝ)..(227 / 110 : ℝ), Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (107 / 55 : ℝ)..(227 / 110 : ℝ), Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t) ≤ (56783444291 / 5000000000000 : ℝ) :=
  quad_log_div_sub (2 / 3 : ℝ) (1 / 3 : ℝ) (1 : ℝ) (1 : ℝ) (107 / 55 : ℝ) (227 / 110 : ℝ) (441 / 220 : ℝ) (13 / 220 : ℝ)
    (881 / 660 : ℝ) (661 / 220 : ℝ) (220 / 881 : ℝ) (220 / 661 : ℝ) (220 / 661 : ℝ) (577635581831 / 2000000000000 : ℝ) (2888177909159 / 10000000000000 : ℝ) (113566888557 / 10000000000000 : ℝ) (56783444291 / 5000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog_65 (by norm_num [quadLogLo]) (by norm_num [quadLogHi])

private lemma hlog_67 : (3179026150943 / 10000000000000 : ℝ) ≤ Real.log (907 / 660 : ℝ) ∧ Real.log (907 / 660 : ℝ) ≤ (63580523019 / 200000000000 : ℝ) :=
  log_rat_bounds (907 / 660 : ℝ) (8 / 899 : ℝ) (-2) (3) (-1) (3179026150943 / 10000000000000 : ℝ) (63580523019 / 200000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hqsub_68 :
    IntervalIntegrable (fun t => Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t)) volume (227 / 110 : ℝ) (24 / 11 : ℝ) ∧
      (120279666879 / 10000000000000 : ℝ) ≤ ∫ t in (227 / 110 : ℝ)..(24 / 11 : ℝ), Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (227 / 110 : ℝ)..(24 / 11 : ℝ), Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t) ≤ (120279666899 / 10000000000000 : ℝ) :=
  quad_log_div_sub (2 / 3 : ℝ) (1 / 3 : ℝ) (1 : ℝ) (1 : ℝ) (227 / 110 : ℝ) (24 / 11 : ℝ) (467 / 220 : ℝ) (13 / 220 : ℝ)
    (907 / 660 : ℝ) (687 / 220 : ℝ) (220 / 907 : ℝ) (220 / 687 : ℝ) (220 / 687 : ℝ) (3179026150943 / 10000000000000 : ℝ) (63580523019 / 200000000000 : ℝ) (120279666879 / 10000000000000 : ℝ) (120279666899 / 10000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog_67 (by norm_num [quadLogLo]) (by norm_num [quadLogHi])

private lemma hlog_69 : (692330731653 / 2000000000000 : ℝ) ≤ Real.log (311 / 220 : ℝ) ∧ Real.log (311 / 220 : ℝ) ≤ (108176676821 / 312500000000 : ℝ) :=
  log_rat_bounds (311 / 220 : ℝ) (13 / 4963 : ℝ) (-5) (2) (1) (692330731653 / 2000000000000 : ℝ) (108176676821 / 312500000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hqsub_70 :
    IntervalIntegrable (fun t => Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t)) volume (24 / 11 : ℝ) (23 / 10 : ℝ) ∧
      (63101355337 / 5000000000000 : ℝ) ≤ ∫ t in (24 / 11 : ℝ)..(23 / 10 : ℝ), Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (24 / 11 : ℝ)..(23 / 10 : ℝ), Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t) ≤ (126202710689 / 10000000000000 : ℝ) :=
  quad_log_div_sub (2 / 3 : ℝ) (1 / 3 : ℝ) (1 : ℝ) (1 : ℝ) (24 / 11 : ℝ) (23 / 10 : ℝ) (493 / 220 : ℝ) (13 / 220 : ℝ)
    (311 / 220 : ℝ) (713 / 220 : ℝ) (220 / 933 : ℝ) (220 / 713 : ℝ) (220 / 713 : ℝ) (692330731653 / 2000000000000 : ℝ) (108176676821 / 312500000000 : ℝ) (63101355337 / 5000000000000 : ℝ) (126202710689 / 10000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog_69 (by norm_num [quadLogLo]) (by norm_num [quadLogHi])

private lemma hqchain_71 :
    IntervalIntegrable (fun t => Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t)) volume (1 : ℝ) (68 / 55 : ℝ) ∧
      (10525980893 / 2500000000000 : ℝ) ≤ ∫ t in (1 : ℝ)..(68 / 55 : ℝ), Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (1 : ℝ)..(68 / 55 : ℝ), Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t) ≤ (8420784823 / 2000000000000 : ℝ) :=
  chain_int_bounds hqsub_50 hqsub_52 (by norm_num) (by norm_num)

private lemma hqchain_72 :
    IntervalIntegrable (fun t => Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t)) volume (1 : ℝ) (149 / 110 : ℝ) ∧
      (18073738159 / 2000000000000 : ℝ) ≤ ∫ t in (1 : ℝ)..(149 / 110 : ℝ), Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (1 : ℝ)..(149 / 110 : ℝ), Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t) ≤ (22592172873 / 2500000000000 : ℝ) :=
  chain_int_bounds hqchain_71 hqsub_54 (by norm_num) (by norm_num)

private lemma hqchain_73 :
    IntervalIntegrable (fun t => Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t)) volume (1 : ℝ) (81 / 55 : ℝ) ∧
      (153532701897 / 10000000000000 : ℝ) ≤ ∫ t in (1 : ℝ)..(81 / 55 : ℝ), Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (1 : ℝ)..(81 / 55 : ℝ), Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t) ≤ (153532702703 / 10000000000000 : ℝ) :=
  chain_int_bounds hqchain_72 hqsub_56 (by norm_num) (by norm_num)

private lemma hqchain_74 :
    IntervalIntegrable (fun t => Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t)) volume (1 : ℝ) (35 / 22 : ℝ) ∧
      (229643744029 / 10000000000000 : ℝ) ≤ ∫ t in (1 : ℝ)..(35 / 22 : ℝ), Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (1 : ℝ)..(35 / 22 : ℝ), Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t) ≤ (229643744913 / 10000000000000 : ℝ) :=
  chain_int_bounds hqchain_73 hqsub_58 (by norm_num) (by norm_num)

private lemma hqchain_75 :
    IntervalIntegrable (fun t => Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t)) volume (1 : ℝ) (94 / 55 : ℝ) ∧
      (79261563429 / 2500000000000 : ℝ) ≤ ∫ t in (1 : ℝ)..(94 / 55 : ℝ), Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (1 : ℝ)..(94 / 55 : ℝ), Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t) ≤ (317046254657 / 10000000000000 : ℝ) :=
  chain_int_bounds hqchain_74 hqsub_60 (by norm_num) (by norm_num)

private lemma hqchain_76 :
    IntervalIntegrable (fun t => Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t)) volume (1 : ℝ) (201 / 110 : ℝ) ∧
      (103581846063 / 2500000000000 : ℝ) ≤ ∫ t in (1 : ℝ)..(201 / 110 : ℝ), Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (1 : ℝ)..(201 / 110 : ℝ), Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t) ≤ (103581846309 / 2500000000000 : ℝ) :=
  chain_int_bounds hqchain_75 hqsub_62 (by norm_num) (by norm_num)

private lemma hqchain_77 :
    IntervalIntegrable (fun t => Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t)) volume (1 : ℝ) (107 / 55 : ℝ) ∧
      (260137253969 / 5000000000000 : ℝ) ≤ ∫ t in (1 : ℝ)..(107 / 55 : ℝ), Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (1 : ℝ)..(107 / 55 : ℝ), Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t) ≤ (260137254477 / 5000000000000 : ℝ) :=
  chain_int_bounds hqchain_76 hqsub_64 (by norm_num) (by norm_num)

private lemma hqchain_78 :
    IntervalIntegrable (fun t => Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t)) volume (1 : ℝ) (227 / 110 : ℝ) ∧
      (126768279299 / 2000000000000 : ℝ) ≤ ∫ t in (1 : ℝ)..(227 / 110 : ℝ), Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (1 : ℝ)..(227 / 110 : ℝ), Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t) ≤ (19807543673 / 312500000000 : ℝ) :=
  chain_int_bounds hqchain_77 hqsub_66 (by norm_num) (by norm_num)

private lemma hqchain_79 :
    IntervalIntegrable (fun t => Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t)) volume (1 : ℝ) (24 / 11 : ℝ) ∧
      (377060531687 / 5000000000000 : ℝ) ≤ ∫ t in (1 : ℝ)..(24 / 11 : ℝ), Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (1 : ℝ)..(24 / 11 : ℝ), Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t) ≤ (150824212887 / 2000000000000 : ℝ) :=
  chain_int_bounds hqchain_78 hqsub_68 (by norm_num) (by norm_num)

private lemma hqchain_80 :
    IntervalIntegrable (fun t => Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t)) volume (1 : ℝ) (23 / 10 : ℝ) ∧
      (27510117939 / 312500000000 : ℝ) ≤ ∫ t in (1 : ℝ)..(23 / 10 : ℝ), Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (1 : ℝ)..(23 / 10 : ℝ), Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t) ≤ (220080943781 / 2500000000000 : ℝ) :=
  chain_int_bounds hqchain_79 hqsub_70 (by norm_num) (by norm_num)

private lemma hfga_48 : (27510117939 / 312500000000 : ℝ) ≤ ∫ s in (1 : ℝ)..(23 / 10 : ℝ), Real.log ((s + 2) / 3) / (s + 1) := by
  refine le_trans hqchain_80.2.1 (le_of_eq ?_)
  apply integral_congr; intro s _; dsimp only; congr 1
  · congr 1; ring
  · ring

private lemma hlog_81 : (85119228837 / 2000000000000 : ℝ) ≤ Real.log (24 / 23 : ℝ) ∧ Real.log (24 / 23 : ℝ) ≤ (425596144191 / 10000000000000 : ℝ) :=
  log_rat_bounds (24 / 23 : ℝ) (1 / 1151 : ℝ) (-3) (-1) (2) (85119228837 / 2000000000000 : ℝ) (425596144191 / 10000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hlog_82 : (382212128197 / 10000000000000 : ℝ) ≤ Real.log (80 / 77 : ℝ) ∧ Real.log (80 / 77 : ℝ) ≤ (382212128207 / 10000000000000 : ℝ) :=
  log_rat_bounds (80 / 77 : ℝ) (9 / 1241 : ℝ) (7) (0) (-3) (382212128197 / 10000000000000 : ℝ) (382212128207 / 10000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hlog_83 : (3623256154471 / 10000000000000 : ℝ) ≤ Real.log (431 / 300 : ℝ) ∧ Real.log (431 / 300 : ℝ) ≤ (3623256154479 / 10000000000000 : ℝ) :=
  log_rat_bounds (431 / 300 : ℝ) (13 / 2573 : ℝ) (6) (-2) (-1) (3623256154471 / 10000000000000 : ℝ) (3623256154479 / 10000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hpsub_84 :
    IntervalIntegrable (fun t => Real.log ((12 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1)) volume (23 / 10 : ℝ) (58 / 25 : ℝ) ∧
      (83672539 / 1000000000000 : ℝ) ≤ ∫ t in (23 / 10 : ℝ)..(58 / 25 : ℝ), Real.log ((12 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1) :=
  quad_prod_log_div_sub (12 / 5 : ℝ) (80 / 77 : ℝ) (431 / 300 : ℝ) (23 / 10 : ℝ) (58 / 25 : ℝ) (231 / 100 : ℝ) (1 / 100 : ℝ)
    (100 / 231 : ℝ) (100 / 431 : ℝ) (100 / 331 : ℝ) (1384852445803239086718787 / 100000000000000000000000000 : ℝ) (-5014607541545781426712809152507 / 32954691000000000000000000000000 : ℝ) (-234008073331256270929276007967250573 / 10860116589054810000000000000000000000 : ℝ) (324930496481871023310555263947682302895359 / 10736753592488257368411300000000000000000000 : ℝ)
    (382212128197 / 10000000000000 : ℝ) (382212128207 / 10000000000000 : ℝ) (3623256154471 / 10000000000000 : ℝ) (3623256154479 / 10000000000000 : ℝ) (83672539 / 1000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hlog_82 hlog_83 (by norm_num [quadProdLo])

private lemma hlog_85 : (148002348879 / 5000000000000 : ℝ) ≤ Real.log (240 / 233 : ℝ) ∧ Real.log (240 / 233 : ℝ) ≤ (37000587221 / 1250000000000 : ℝ) :=
  log_rat_bounds (240 / 233 : ℝ) (11 / 3739 : ℝ) (7) (0) (-3) (148002348879 / 5000000000000 : ℝ) (37000587221 / 1250000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hlog_86 : (3669552533459 / 10000000000000 : ℝ) ≤ Real.log (433 / 300 : ℝ) ∧ Real.log (433 / 300 : ℝ) ≤ (1834776266733 / 5000000000000 : ℝ) :=
  log_rat_bounds (433 / 300 : ℝ) (1 / 865 : ℝ) (2) (2) (-2) (3669552533459 / 10000000000000 : ℝ) (1834776266733 / 5000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hpsub_87 :
    IntervalIntegrable (fun t => Real.log ((12 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1)) volume (58 / 25 : ℝ) (117 / 50 : ℝ) ∧
      (65233537 / 1000000000000 : ℝ) ≤ ∫ t in (58 / 25 : ℝ)..(117 / 50 : ℝ), Real.log ((12 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1) :=
  quad_prod_log_div_sub (12 / 5 : ℝ) (240 / 233 : ℝ) (433 / 300 : ℝ) (58 / 25 : ℝ) (117 / 50 : ℝ) (233 / 100 : ℝ) (1 / 100 : ℝ)
    (100 / 233 : ℝ) (100 / 433 : ℝ) (100 / 333 : ℝ) (543102394286817238642461 / 50000000000000000000000000 : ℝ) (-287278340691119349932155471981 / 1866446500000000000000000000000 : ℝ) (-12472291282673287147522266587308891 / 627052056725205000000000000000000000 : ℝ) (6138852195688476098073288218727006704099 / 210664640986660860125850000000000000000000 : ℝ)
    (148002348879 / 5000000000000 : ℝ) (37000587221 / 1250000000000 : ℝ) (3669552533459 / 10000000000000 : ℝ) (1834776266733 / 5000000000000 : ℝ) (65233537 / 1000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hlog_85 hlog_86 (by norm_num [quadProdLo])

private lemma hlog_88 : (105267045987 / 5000000000000 : ℝ) ≤ Real.log (48 / 47 : ℝ) ∧ Real.log (48 / 47 : ℝ) ≤ (210534091983 / 10000000000000 : ℝ) :=
  log_rat_bounds (48 / 47 : ℝ) (11 / 2549 : ℝ) (-4) (4) (-1) (105267045987 / 5000000000000 : ℝ) (210534091983 / 10000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hlog_89 : (3715635564321 / 10000000000000 : ℝ) ≤ Real.log (29 / 20 : ℝ) ∧ Real.log (29 / 20 : ℝ) ≤ (464454445541 / 1250000000000 : ℝ) :=
  log_rat_bounds (29 / 20 : ℝ) (1 / 289 : ℝ) (2) (2) (-2) (3715635564321 / 10000000000000 : ℝ) (464454445541 / 1250000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hpsub_90 :
    IntervalIntegrable (fun t => Real.log ((12 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1)) volume (117 / 50 : ℝ) (59 / 25 : ℝ) ∧
      (116747299 / 2500000000000 : ℝ) ≤ ∫ t in (117 / 50 : ℝ)..(59 / 25 : ℝ), Real.log ((12 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1) :=
  quad_prod_log_div_sub (12 / 5 : ℝ) (48 / 47 : ℝ) (29 / 20 : ℝ) (117 / 50 : ℝ) (59 / 25 : ℝ) (47 / 20 : ℝ) (1 / 100 : ℝ)
    (20 / 47 : ℝ) (20 / 87 : ℝ) (20 / 67 : ℝ) (391133979820311403429827 / 50000000000000000000000000 : ℝ) (-35525562029163389442874854201 / 228302500000000000000000000000 : ℝ) (-57195204642968444245584721172111 / 3127321890375000000000000000000000 : ℝ) (1201992386077566300098560924872761879 / 42838524352640306250000000000000000000 : ℝ)
    (105267045987 / 5000000000000 : ℝ) (210534091983 / 10000000000000 : ℝ) (3715635564321 / 10000000000000 : ℝ) (464454445541 / 1250000000000 : ℝ) (116747299 / 2500000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hlog_88 hlog_89 (by norm_num [quadProdLo])

private lemma hlog_91 : (7861738879 / 625000000000 : ℝ) ≤ Real.log (80 / 79 : ℝ) ∧ Real.log (80 / 79 : ℝ) ≤ (125787822073 / 10000000000000 : ℝ) :=
  log_rat_bounds (80 / 79 : ℝ) (1 / 12799 : ℝ) (-4) (4) (-1) (7861738879 / 625000000000 : ℝ) (125787822073 / 10000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hlog_92 : (376150720439 / 1000000000000 : ℝ) ≤ Real.log (437 / 300 : ℝ) ∧ Real.log (437 / 300 : ℝ) ≤ (3761507204397 / 10000000000000 : ℝ) :=
  log_rat_bounds (437 / 300 : ℝ) (5 / 869 : ℝ) (2) (2) (-2) (376150720439 / 1000000000000 : ℝ) (3761507204397 / 10000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hpsub_93 :
    IntervalIntegrable (fun t => Real.log ((12 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1)) volume (59 / 25 : ℝ) (119 / 50 : ℝ) ∧
      (280769083 / 10000000000000 : ℝ) ≤ ∫ t in (59 / 25 : ℝ)..(119 / 50 : ℝ), Real.log ((12 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1) :=
  quad_prod_log_div_sub (12 / 5 : ℝ) (80 / 79 : ℝ) (437 / 300 : ℝ) (59 / 25 : ℝ) (119 / 50 : ℝ) (237 / 100 : ℝ) (1 / 100 : ℝ)
    (100 / 237 : ℝ) (100 / 437 : ℝ) (100 / 337 : ℝ) (2957198743239146247881 / 625000000000000000000000 : ℝ) (-34300452674318616012746787289 / 218142206250000000000000000000 : ℝ) (-1274623885793846464285640487265559 / 76137635436188062500000000000000000 : ℝ) (2153821543544587479910189853001820040213 / 79722392508999576209581875000000000000000 : ℝ)
    (7861738879 / 625000000000 : ℝ) (125787822073 / 10000000000000 : ℝ) (376150720439 / 1000000000000 : ℝ) (3761507204397 / 10000000000000 : ℝ) (280769083 / 10000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hlog_91 hlog_92 (by norm_num [quadProdLo])

private lemma hlog_94 : (5219214263 / 1250000000000 : ℝ) ≤ Real.log (240 / 239 : ℝ) ∧ Real.log (240 / 239 : ℝ) ≤ (8350742821 / 2000000000000 : ℝ) :=
  log_rat_bounds (240 / 239 : ℝ) (1 / 479 : ℝ) (0) (0) (0) (5219214263 / 1250000000000 : ℝ) (8350742821 / 2000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hlog_95 : (1903584692093 / 5000000000000 : ℝ) ≤ Real.log (439 / 300 : ℝ) ∧ Real.log (439 / 300 : ℝ) ≤ (3807169384193 / 10000000000000 : ℝ) :=
  log_rat_bounds (439 / 300 : ℝ) (7 / 871 : ℝ) (2) (2) (-2) (1903584692093 / 5000000000000 : ℝ) (3807169384193 / 10000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hpsub_96 :
    IntervalIntegrable (fun t => Real.log ((12 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1)) volume (119 / 50 : ℝ) (12 / 5 : ℝ) ∧
      (46876861 / 5000000000000 : ℝ) ≤ ∫ t in (119 / 50 : ℝ)..(12 / 5 : ℝ), Real.log ((12 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1) :=
  quad_prod_log_div_sub (12 / 5 : ℝ) (240 / 239 : ℝ) (439 / 300 : ℝ) (119 / 50 : ℝ) (12 / 5 : ℝ) (239 / 100 : ℝ) (1 / 100 : ℝ)
    (100 / 239 : ℝ) (100 / 439 : ℝ) (100 / 339 : ℝ) (9935216375800248922459 / 6250000000000000000000000 : ℝ) (-353044804870818164167193320739 / 2223013687500000000000000000000 : ℝ) (-12054000261976618221238284594743381 / 790686376769975625000000000000000000 : ℝ) (7315520475346162264939374599215070277901 / 281233062092710056546618750000000000000000 : ℝ)
    (5219214263 / 1250000000000 : ℝ) (8350742821 / 2000000000000 : ℝ) (1903584692093 / 5000000000000 : ℝ) (3807169384193 / 10000000000000 : ℝ) (46876861 / 5000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hlog_94 hlog_95 (by norm_num [quadProdLo])

private lemma hpchain_97 :
    IntervalIntegrable (fun t => Real.log ((12 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1)) volume (23 / 10 : ℝ) (117 / 50 : ℝ) ∧
      (37226519 / 250000000000 : ℝ) ≤ ∫ t in (23 / 10 : ℝ)..(117 / 50 : ℝ), Real.log ((12 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1) :=
  chain_int_lb hpsub_84 hpsub_87 (by norm_num)

private lemma hpchain_98 :
    IntervalIntegrable (fun t => Real.log ((12 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1)) volume (23 / 10 : ℝ) (59 / 25 : ℝ) ∧
      (489012489 / 2500000000000 : ℝ) ≤ ∫ t in (23 / 10 : ℝ)..(59 / 25 : ℝ), Real.log ((12 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1) :=
  chain_int_lb hpchain_97 hpsub_90 (by norm_num)

private lemma hpchain_99 :
    IntervalIntegrable (fun t => Real.log ((12 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1)) volume (23 / 10 : ℝ) (119 / 50 : ℝ) ∧
      (2236819039 / 10000000000000 : ℝ) ≤ ∫ t in (23 / 10 : ℝ)..(119 / 50 : ℝ), Real.log ((12 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1) :=
  chain_int_lb hpchain_98 hpsub_93 (by norm_num)

private lemma hpchain_100 :
    IntervalIntegrable (fun t => Real.log ((12 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1)) volume (23 / 10 : ℝ) (12 / 5 : ℝ) ∧
      (2330572761 / 10000000000000 : ℝ) ≤ ∫ t in (23 / 10 : ℝ)..(12 / 5 : ℝ), Real.log ((12 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1) :=
  chain_int_lb hpchain_99 hpsub_96 (by norm_num)

private lemma hlog_101 : (17751536095797 / 5000000000000 : ℝ) ≤ Real.log (800000000 / 22972653 : ℝ) ∧ Real.log (800000000 / 22972653 : ℝ) ≤ (8875768047901 / 2500000000000 : ℝ) :=
  log_rat_bounds (800000000 / 22972653 : ℝ) (4738369 / 1245261631 : ℝ) (5) (3) (-2) (17751536095797 / 5000000000000 : ℝ) (8875768047901 / 2500000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hterm_s0_102 :
    IntervalIntegrable (fun t => sigma0 t / ((5 : ℝ) * t) * Real.log (800000000 / 22972653 : ℝ)) volume (23 / 10 : ℝ) (12 / 5 : ℝ) ∧
      (6823121601 / 2000000000000 : ℝ) ≤ ∫ t in (23 / 10 : ℝ)..(12 / 5 : ℝ), sigma0 t / ((5 : ℝ) * t) * Real.log (800000000 / 22972653 : ℝ) :=
  bound_sigma0_term (5 : ℝ) (800000000 / 22972653 : ℝ) (23 / 10 : ℝ) (12 / 5 : ℝ) (24 / 23 : ℝ)
    (85846709821 / 500000000000 : ℝ) (1716934197987 / 10000000000000 : ℝ) (27510117939 / 312500000000 : ℝ) (85119228837 / 2000000000000 : ℝ) (425596144191 / 10000000000000 : ℝ) (2330572761 / 10000000000000 : ℝ) (17751536095797 / 5000000000000 : ℝ) (8875768047901 / 2500000000000 : ℝ) (6823121601 / 2000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hqchain_47 (by norm_num) hfga_48 hlog_81 hpchain_100.2 hlog_101
    (by norm_num) (by norm_num) (by norm_num)

private lemma hterm_103 :
    IntervalIntegrable (fun t => ind (127 / 50 : ℝ) (3 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) ^ (5 : ℕ) / (22972653 / 781250 : ℝ))) volume (23 / 10 : ℝ) (12 / 5 : ℝ) ∧
      (0 : ℝ) ≤ ∫ t in (23 / 10 : ℝ)..(12 / 5 : ℝ), ind (127 / 50 : ℝ) (3 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) ^ (5 : ℕ) / (22972653 / 781250 : ℝ)) :=
  bound_ind_div_zero (23 / 10 : ℝ) (12 / 5 : ℝ) (127 / 50 : ℝ) (3 : ℝ) (fun t => (5 : ℝ) * t) (fun t => (t + 1) ^ (5 : ℕ) / (22972653 / 781250 : ℝ)) (by norm_num) (Or.inr (by norm_num))

private lemma hterm_104 :
    IntervalIntegrable (fun t => ind (3807 / 2900 : ℝ) (153 / 100 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) / ((19 / 10 : ℝ) * ((253 / 100 : ℝ) - t)))) volume (23 / 10 : ℝ) (12 / 5 : ℝ) ∧
      (0 : ℝ) ≤ ∫ t in (23 / 10 : ℝ)..(12 / 5 : ℝ), ind (3807 / 2900 : ℝ) (153 / 100 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) / ((19 / 10 : ℝ) * ((253 / 100 : ℝ) - t))) :=
  bound_ind_div_zero (23 / 10 : ℝ) (12 / 5 : ℝ) (3807 / 2900 : ℝ) (153 / 100 : ℝ) (fun t => (5 : ℝ) * t) (fun t => (t + 1) / ((19 / 10 : ℝ) * ((253 / 100 : ℝ) - t))) (by norm_num) (Or.inl (by norm_num))

private lemma hlog_106 : (29171449087 / 80000000000 : ℝ) ≤ Real.log (36 / 25 : ℝ) ∧ Real.log (36 / 25 : ℝ) ≤ (1823215567941 / 5000000000000 : ℝ) :=
  log_rat_bounds (36 / 25 : ℝ) (0 : ℝ) (2) (2) (-2) (29171449087 / 80000000000 : ℝ) (1823215567941 / 5000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hlog_107 : (12089603458367 / 10000000000000 : ℝ) ≤ Real.log (67 / 20 : ℝ) ∧ Real.log (67 / 20 : ℝ) ≤ (12089603458371 / 10000000000000 : ℝ) :=
  log_rat_bounds (67 / 20 : ℝ) (1 / 401 : ℝ) (1) (-1) (1) (12089603458367 / 10000000000000 : ℝ) (12089603458371 / 10000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hqsub_108 :
    IntervalIntegrable (fun t => Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t)) volume (23 / 10 : ℝ) (12 / 5 : ℝ) ∧
      (102893599771 / 2000000000000 : ℝ) ≤ ∫ t in (23 / 10 : ℝ)..(12 / 5 : ℝ), Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (23 / 10 : ℝ)..(12 / 5 : ℝ), Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ≤ (514467998903 / 10000000000000 : ℝ) :=
  quad_log_div_sub (1 : ℝ) (1 : ℝ) (0 : ℝ) (1 : ℝ) (23 / 10 : ℝ) (12 / 5 : ℝ) (47 / 20 : ℝ) (1 / 20 : ℝ)
    (67 / 20 : ℝ) (47 / 20 : ℝ) (20 / 67 : ℝ) (20 / 47 : ℝ) (20 / 47 : ℝ) (12089603458367 / 10000000000000 : ℝ) (12089603458371 / 10000000000000 : ℝ) (102893599771 / 2000000000000 : ℝ) (514467998903 / 10000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog_107 (by norm_num [quadLogLo]) (by norm_num [quadLogHi])

private lemma hlog_109 : (1739533071231 / 10000000000000 : ℝ) ≤ Real.log (119 / 100 : ℝ) ∧ Real.log (119 / 100 : ℝ) ≤ (869766535619 / 5000000000000 : ℝ) :=
  log_rat_bounds (119 / 100 : ℝ) (13 / 6413 : ℝ) (5) (-3) (0) (1739533071231 / 10000000000000 : ℝ) (869766535619 / 5000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hqsub_110 :
    IntervalIntegrable (fun t => Real.log ((177 / 50 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t)) volume (23 / 10 : ℝ) (12 / 5 : ℝ) ∧
      (18508858221 / 2500000000000 : ℝ) ≤ ∫ t in (23 / 10 : ℝ)..(12 / 5 : ℝ), Real.log ((177 / 50 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (23 / 10 : ℝ)..(12 / 5 : ℝ), Real.log ((177 / 50 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ≤ (18508858807 / 2500000000000 : ℝ) :=
  quad_log_div_sub (177 / 50 : ℝ) (-1 : ℝ) (0 : ℝ) (1 : ℝ) (23 / 10 : ℝ) (12 / 5 : ℝ) (47 / 20 : ℝ) (1 / 20 : ℝ)
    (119 / 100 : ℝ) (47 / 20 : ℝ) (-100 / 119 : ℝ) (20 / 47 : ℝ) (100 / 119 : ℝ) (1739533071231 / 10000000000000 : ℝ) (869766535619 / 5000000000000 : ℝ) (18508858221 / 2500000000000 : ℝ) (18508858807 / 2500000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog_109 (by norm_num [quadLogLo]) (by norm_num [quadLogHi])

private lemma hact_tl_111 :
    IntervalIntegrable (fun t => Real.log ((t + 1) / ((36 / 25 : ℝ) * ((177 / 50 : ℝ) - t))) / ((5 : ℝ) * t)) volume (23 / 10 : ℝ) (12 / 5 : ℝ) ∧
      (11409674419 / 2000000000000 : ℝ) ≤ ∫ t in (23 / 10 : ℝ)..(12 / 5 : ℝ), Real.log ((t + 1) / ((36 / 25 : ℝ) * ((177 / 50 : ℝ) - t))) / ((5 : ℝ) * t) :=
  active_t_lin (5 : ℝ) (36 / 25 : ℝ) (177 / 50 : ℝ) (23 / 10 : ℝ) (12 / 5 : ℝ) (24 / 23 : ℝ) (29171449087 / 80000000000 : ℝ) (1823215567941 / 5000000000000 : ℝ) (85119228837 / 2000000000000 : ℝ) (425596144191 / 10000000000000 : ℝ)
    (102893599771 / 2000000000000 : ℝ) (514467998903 / 10000000000000 : ℝ) (18508858221 / 2500000000000 : ℝ) (18508858807 / 2500000000000 : ℝ) (11409674419 / 2000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog_106 hlog_81 hqsub_108 hqsub_110 (by norm_num)

private lemma hterm_105 :
    IntervalIntegrable (fun t => ind (2561 / 1525 : ℝ) (127 / 50 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) / ((36 / 25 : ℝ) * ((177 / 50 : ℝ) - t)))) volume (23 / 10 : ℝ) (12 / 5 : ℝ) ∧
      (11409674419 / 2000000000000 : ℝ) ≤ ∫ t in (23 / 10 : ℝ)..(12 / 5 : ℝ), ind (2561 / 1525 : ℝ) (127 / 50 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) / ((36 / 25 : ℝ) * ((177 / 50 : ℝ) - t))) :=
  bound_ind_div_active (23 / 10 : ℝ) (12 / 5 : ℝ) (2561 / 1525 : ℝ) (127 / 50 : ℝ) (23 / 10 : ℝ) (12 / 5 : ℝ) (11409674419 / 2000000000000 : ℝ)
    (fun t => (5 : ℝ) * t) (fun t => (t + 1) / ((36 / 25 : ℝ) * ((177 / 50 : ℝ) - t)))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (Or.inl rfl) (Or.inl rfl) hact_tl_111

private lemma hlog_113 : (1823215567937 / 10000000000000 : ℝ) ≤ Real.log (6 / 5 : ℝ) ∧ Real.log (6 / 5 : ℝ) ≤ (1823215567941 / 10000000000000 : ℝ) :=
  log_rat_bounds (6 / 5 : ℝ) (0 : ℝ) (1) (1) (-1) (1823215567937 / 10000000000000 : ℝ) (1823215567941 / 10000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hact_tl_114 :
    IntervalIntegrable (fun t => Real.log ((t + 1) / ((6 / 5 : ℝ) * ((177 / 50 : ℝ) - t))) / ((5 : ℝ) * t)) volume (23 / 10 : ℝ) (12 / 5 : ℝ) ∧
      (7256744241 / 1000000000000 : ℝ) ≤ ∫ t in (23 / 10 : ℝ)..(12 / 5 : ℝ), Real.log ((t + 1) / ((6 / 5 : ℝ) * ((177 / 50 : ℝ) - t))) / ((5 : ℝ) * t) :=
  active_t_lin (5 : ℝ) (6 / 5 : ℝ) (177 / 50 : ℝ) (23 / 10 : ℝ) (12 / 5 : ℝ) (24 / 23 : ℝ) (1823215567937 / 10000000000000 : ℝ) (1823215567941 / 10000000000000 : ℝ) (85119228837 / 2000000000000 : ℝ) (425596144191 / 10000000000000 : ℝ)
    (102893599771 / 2000000000000 : ℝ) (514467998903 / 10000000000000 : ℝ) (18508858221 / 2500000000000 : ℝ) (18508858807 / 2500000000000 : ℝ) (7256744241 / 1000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog_113 hlog_81 hqsub_108 hqsub_110 (by norm_num)

private lemma hterm_112 :
    IntervalIntegrable (fun t => ind (406 / 275 : ℝ) (127 / 50 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) / ((6 / 5 : ℝ) * ((177 / 50 : ℝ) - t)))) volume (23 / 10 : ℝ) (12 / 5 : ℝ) ∧
      (7256744241 / 1000000000000 : ℝ) ≤ ∫ t in (23 / 10 : ℝ)..(12 / 5 : ℝ), ind (406 / 275 : ℝ) (127 / 50 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) / ((6 / 5 : ℝ) * ((177 / 50 : ℝ) - t))) :=
  bound_ind_div_active (23 / 10 : ℝ) (12 / 5 : ℝ) (406 / 275 : ℝ) (127 / 50 : ℝ) (23 / 10 : ℝ) (12 / 5 : ℝ) (7256744241 / 1000000000000 : ℝ)
    (fun t => (5 : ℝ) * t) (fun t => (t + 1) / ((6 / 5 : ℝ) * ((177 / 50 : ℝ) - t)))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (Or.inl rfl) (Or.inl rfl) hact_tl_114

private lemma hlog_116 : (3140146377823 / 2000000000000 : ℝ) ≤ Real.log (4807 / 1000 : ℝ) ∧ Real.log (4807 / 1000 : ℝ) ≤ (98129574307 / 62500000000 : ℝ) :=
  log_rat_bounds (4807 / 1000 : ℝ) (7 / 9607 : ℝ) (3) (1) (-1) (3140146377823 / 2000000000000 : ℝ) (98129574307 / 62500000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hact_tp_117 :
    IntervalIntegrable (fun t => Real.log ((t + 1) ^ (2 : ℕ) / (4807 / 1000 : ℝ)) / ((5 : ℝ) * t)) volume (23 / 10 : ℝ) (12 / 5 : ℝ) ∧
      (36071890241 / 5000000000000 : ℝ) ≤ ∫ t in (23 / 10 : ℝ)..(12 / 5 : ℝ), Real.log ((t + 1) ^ (2 : ℕ) / (4807 / 1000 : ℝ)) / ((5 : ℝ) * t) :=
  active_t_pow 2 (5 : ℝ) (4807 / 1000 : ℝ) (23 / 10 : ℝ) (12 / 5 : ℝ) (24 / 23 : ℝ) (3140146377823 / 2000000000000 : ℝ) (98129574307 / 62500000000 : ℝ) (85119228837 / 2000000000000 : ℝ) (425596144191 / 10000000000000 : ℝ)
    (102893599771 / 2000000000000 : ℝ) (514467998903 / 10000000000000 : ℝ) (36071890241 / 5000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hlog_116 hlog_81 hqsub_108 (by norm_num)

private lemma hterm_115 :
    IntervalIntegrable (fun t => ind (153 / 100 : ℝ) (127 / 50 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) ^ (2 : ℕ) / (4807 / 1000 : ℝ))) volume (23 / 10 : ℝ) (12 / 5 : ℝ) ∧
      (36071890241 / 5000000000000 : ℝ) ≤ ∫ t in (23 / 10 : ℝ)..(12 / 5 : ℝ), ind (153 / 100 : ℝ) (127 / 50 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) ^ (2 : ℕ) / (4807 / 1000 : ℝ)) :=
  bound_ind_div_active (23 / 10 : ℝ) (12 / 5 : ℝ) (153 / 100 : ℝ) (127 / 50 : ℝ) (23 / 10 : ℝ) (12 / 5 : ℝ) (36071890241 / 5000000000000 : ℝ)
    (fun t => (5 : ℝ) * t) (fun t => (t + 1) ^ (2 : ℕ) / (4807 / 1000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (Or.inl rfl) (Or.inl rfl) hact_tp_117

private lemma hterm_118 :
    IntervalIntegrable (fun t => ind (750008 / 538325 : ℝ) (2561 / 1525 : ℝ) t / (5 * t * (1 - t / (227 / 50 : ℝ))) * Real.log ((227 / 50 : ℝ) ^ (2 : ℕ) / (((353 / 100 : ℝ) * (227 / 50 : ℝ) - (227 / 50 : ℝ) - (353 / 100 : ℝ) * t) * ((61 / 25 : ℝ) * (227 / 50 : ℝ) - (227 / 50 : ℝ) - (61 / 25 : ℝ) * t)))) volume (23 / 10 : ℝ) (12 / 5 : ℝ) ∧
      (0 : ℝ) ≤ ∫ t in (23 / 10 : ℝ)..(12 / 5 : ℝ), ind (750008 / 538325 : ℝ) (2561 / 1525 : ℝ) t / (5 * t * (1 - t / (227 / 50 : ℝ))) * Real.log ((227 / 50 : ℝ) ^ (2 : ℕ) / (((353 / 100 : ℝ) * (227 / 50 : ℝ) - (227 / 50 : ℝ) - (353 / 100 : ℝ) * t) * ((61 / 25 : ℝ) * (227 / 50 : ℝ) - (227 / 50 : ℝ) - (61 / 25 : ℝ) * t))) :=
  bound_ind_div_zero (23 / 10 : ℝ) (12 / 5 : ℝ) (750008 / 538325 : ℝ) (2561 / 1525 : ℝ) (fun t => 5 * t * (1 - t / (227 / 50 : ℝ))) (fun t => (227 / 50 : ℝ) ^ (2 : ℕ) / (((353 / 100 : ℝ) * (227 / 50 : ℝ) - (227 / 50 : ℝ) - (353 / 100 : ℝ) * t) * ((61 / 25 : ℝ) * (227 / 50 : ℝ) - (227 / 50 : ℝ) - (61 / 25 : ℝ) * t))) (by norm_num) (Or.inl (by norm_num))

private lemma hterm_119 :
    IntervalIntegrable (fun t => ind (2561 / 1525 : ℝ) (864189 / 511850 : ℝ) t / (5 * t * (1 - t / (227 / 50 : ℝ))) * Real.log ((227 / 50 : ℝ) * ((227 / 50 : ℝ) - 1 - t) / ((353 / 100 : ℝ) * (227 / 50 : ℝ) - (227 / 50 : ℝ) - (353 / 100 : ℝ) * t))) volume (23 / 10 : ℝ) (12 / 5 : ℝ) ∧
      (0 : ℝ) ≤ ∫ t in (23 / 10 : ℝ)..(12 / 5 : ℝ), ind (2561 / 1525 : ℝ) (864189 / 511850 : ℝ) t / (5 * t * (1 - t / (227 / 50 : ℝ))) * Real.log ((227 / 50 : ℝ) * ((227 / 50 : ℝ) - 1 - t) / ((353 / 100 : ℝ) * (227 / 50 : ℝ) - (227 / 50 : ℝ) - (353 / 100 : ℝ) * t)) :=
  bound_ind_div_zero (23 / 10 : ℝ) (12 / 5 : ℝ) (2561 / 1525 : ℝ) (864189 / 511850 : ℝ) (fun t => 5 * t * (1 - t / (227 / 50 : ℝ))) (fun t => (227 / 50 : ℝ) * ((227 / 50 : ℝ) - 1 - t) / ((353 / 100 : ℝ) * (227 / 50 : ℝ) - (227 / 50 : ℝ) - (353 / 100 : ℝ) * t)) (by norm_num) (Or.inl (by norm_num))

private lemma hterm_120 :
    IntervalIntegrable (fun t => ind (2043 / 1450 : ℝ) (864189 / 511850 : ℝ) t / (5 * t * (1 - t / (227 / 50 : ℝ))) * Real.log ((227 / 50 : ℝ) / ((29 / 10 : ℝ) * (227 / 50 : ℝ) - (227 / 50 : ℝ) - (29 / 10 : ℝ) * t))) volume (23 / 10 : ℝ) (12 / 5 : ℝ) ∧
      (0 : ℝ) ≤ ∫ t in (23 / 10 : ℝ)..(12 / 5 : ℝ), ind (2043 / 1450 : ℝ) (864189 / 511850 : ℝ) t / (5 * t * (1 - t / (227 / 50 : ℝ))) * Real.log ((227 / 50 : ℝ) / ((29 / 10 : ℝ) * (227 / 50 : ℝ) - (227 / 50 : ℝ) - (29 / 10 : ℝ) * t)) :=
  bound_ind_div_zero (23 / 10 : ℝ) (12 / 5 : ℝ) (2043 / 1450 : ℝ) (864189 / 511850 : ℝ) (fun t => 5 * t * (1 - t / (227 / 50 : ℝ))) (fun t => (227 / 50 : ℝ) / ((29 / 10 : ℝ) * (227 / 50 : ℝ) - (227 / 50 : ℝ) - (29 / 10 : ℝ) * t)) (by norm_num) (Or.inl (by norm_num))

private lemma hqsub_122 :
    IntervalIntegrable (fun t => Real.log ((177 / 50 : ℝ) + (-1 : ℝ) * t) / ((227 / 50 : ℝ) + (-1 : ℝ) * t)) volume (23 / 10 : ℝ) (12 / 5 : ℝ) ∧
      (79163963421 / 10000000000000 : ℝ) ≤ ∫ t in (23 / 10 : ℝ)..(12 / 5 : ℝ), Real.log ((177 / 50 : ℝ) + (-1 : ℝ) * t) / ((227 / 50 : ℝ) + (-1 : ℝ) * t) ∧
      ∫ t in (23 / 10 : ℝ)..(12 / 5 : ℝ), Real.log ((177 / 50 : ℝ) + (-1 : ℝ) * t) / ((227 / 50 : ℝ) + (-1 : ℝ) * t) ≤ (79163965937 / 10000000000000 : ℝ) :=
  quad_log_div_sub (177 / 50 : ℝ) (-1 : ℝ) (227 / 50 : ℝ) (-1 : ℝ) (23 / 10 : ℝ) (12 / 5 : ℝ) (47 / 20 : ℝ) (1 / 20 : ℝ)
    (119 / 100 : ℝ) (219 / 100 : ℝ) (-100 / 119 : ℝ) (-100 / 219 : ℝ) (100 / 119 : ℝ) (1739533071231 / 10000000000000 : ℝ) (869766535619 / 5000000000000 : ℝ) (79163963421 / 10000000000000 : ℝ) (79163965937 / 10000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog_109 (by norm_num [quadLogLo]) (by norm_num [quadLogHi])

private lemma hact_q9_123 :
    IntervalIntegrable (fun t => Real.log ((227 / 50 : ℝ) - 1 - t) / (5 * t * (1 - t / (227 / 50 : ℝ)))) volume (23 / 10 : ℝ) (12 / 5 : ℝ) ∧
      (30639879261 / 10000000000000 : ℝ) ≤ ∫ t in (23 / 10 : ℝ)..(12 / 5 : ℝ), Real.log ((227 / 50 : ℝ) - 1 - t) / (5 * t * (1 - t / (227 / 50 : ℝ))) :=
  active_q_9 (227 / 50 : ℝ) (177 / 50 : ℝ) (23 / 10 : ℝ) (12 / 5 : ℝ)
    (18508858221 / 2500000000000 : ℝ) (18508858807 / 2500000000000 : ℝ) (79163963421 / 10000000000000 : ℝ) (79163965937 / 10000000000000 : ℝ) (30639879261 / 10000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hqsub_110 hqsub_122 (by norm_num)

private lemma hterm_121 :
    IntervalIntegrable (fun t => ind (864189 / 511850 : ℝ) (127 / 50 : ℝ) t / (5 * t * (1 - t / (227 / 50 : ℝ))) * Real.log ((227 / 50 : ℝ) - 1 - t)) volume (23 / 10 : ℝ) (12 / 5 : ℝ) ∧
      (30639879261 / 10000000000000 : ℝ) ≤ ∫ t in (23 / 10 : ℝ)..(12 / 5 : ℝ), ind (864189 / 511850 : ℝ) (127 / 50 : ℝ) t / (5 * t * (1 - t / (227 / 50 : ℝ))) * Real.log ((227 / 50 : ℝ) - 1 - t) :=
  bound_ind_div_active (23 / 10 : ℝ) (12 / 5 : ℝ) (864189 / 511850 : ℝ) (127 / 50 : ℝ) (23 / 10 : ℝ) (12 / 5 : ℝ) (30639879261 / 10000000000000 : ℝ)
    (fun t => 5 * t * (1 - t / (227 / 50 : ℝ))) (fun t => (227 / 50 : ℝ) - 1 - t)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (Or.inl rfl) (Or.inl rfl) hact_q9_123

private lemma hsum_124 :
    IntervalIntegrable (fun t => (sigma0 t / ((5 : ℝ) * t) * Real.log (800000000 / 22972653 : ℝ)) + (ind (127 / 50 : ℝ) (3 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) ^ (5 : ℕ) / (22972653 / 781250 : ℝ)))) volume (23 / 10 : ℝ) (12 / 5 : ℝ) ∧
      (6823121601 / 2000000000000 : ℝ) ≤ ∫ t in (23 / 10 : ℝ)..(12 / 5 : ℝ), ((sigma0 t / ((5 : ℝ) * t) * Real.log (800000000 / 22972653 : ℝ)) + (ind (127 / 50 : ℝ) (3 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) ^ (5 : ℕ) / (22972653 / 781250 : ℝ)))) :=
  add_int_lb hterm_s0_102 hterm_103 (by norm_num)

private lemma hsum_125 :
    IntervalIntegrable (fun t => ((sigma0 t / ((5 : ℝ) * t) * Real.log (800000000 / 22972653 : ℝ)) + (ind (127 / 50 : ℝ) (3 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) ^ (5 : ℕ) / (22972653 / 781250 : ℝ)))) + (ind (3807 / 2900 : ℝ) (153 / 100 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) / ((19 / 10 : ℝ) * ((253 / 100 : ℝ) - t))))) volume (23 / 10 : ℝ) (12 / 5 : ℝ) ∧
      (6823121601 / 2000000000000 : ℝ) ≤ ∫ t in (23 / 10 : ℝ)..(12 / 5 : ℝ), (((sigma0 t / ((5 : ℝ) * t) * Real.log (800000000 / 22972653 : ℝ)) + (ind (127 / 50 : ℝ) (3 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) ^ (5 : ℕ) / (22972653 / 781250 : ℝ)))) + (ind (3807 / 2900 : ℝ) (153 / 100 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) / ((19 / 10 : ℝ) * ((253 / 100 : ℝ) - t))))) :=
  add_int_lb hsum_124 hterm_104 (by norm_num)

private lemma hsum_126 :
    IntervalIntegrable (fun t => (((sigma0 t / ((5 : ℝ) * t) * Real.log (800000000 / 22972653 : ℝ)) + (ind (127 / 50 : ℝ) (3 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) ^ (5 : ℕ) / (22972653 / 781250 : ℝ)))) + (ind (3807 / 2900 : ℝ) (153 / 100 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) / ((19 / 10 : ℝ) * ((253 / 100 : ℝ) - t))))) + (ind (2561 / 1525 : ℝ) (127 / 50 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) / ((36 / 25 : ℝ) * ((177 / 50 : ℝ) - t))))) volume (23 / 10 : ℝ) (12 / 5 : ℝ) ∧
      (911639801 / 100000000000 : ℝ) ≤ ∫ t in (23 / 10 : ℝ)..(12 / 5 : ℝ), ((((sigma0 t / ((5 : ℝ) * t) * Real.log (800000000 / 22972653 : ℝ)) + (ind (127 / 50 : ℝ) (3 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) ^ (5 : ℕ) / (22972653 / 781250 : ℝ)))) + (ind (3807 / 2900 : ℝ) (153 / 100 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) / ((19 / 10 : ℝ) * ((253 / 100 : ℝ) - t))))) + (ind (2561 / 1525 : ℝ) (127 / 50 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) / ((36 / 25 : ℝ) * ((177 / 50 : ℝ) - t))))) :=
  add_int_lb hsum_125 hterm_105 (by norm_num)

private lemma hsum_127 :
    IntervalIntegrable (fun t => ((((sigma0 t / ((5 : ℝ) * t) * Real.log (800000000 / 22972653 : ℝ)) + (ind (127 / 50 : ℝ) (3 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) ^ (5 : ℕ) / (22972653 / 781250 : ℝ)))) + (ind (3807 / 2900 : ℝ) (153 / 100 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) / ((19 / 10 : ℝ) * ((253 / 100 : ℝ) - t))))) + (ind (2561 / 1525 : ℝ) (127 / 50 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) / ((36 / 25 : ℝ) * ((177 / 50 : ℝ) - t))))) + (ind (406 / 275 : ℝ) (127 / 50 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) / ((6 / 5 : ℝ) * ((177 / 50 : ℝ) - t))))) volume (23 / 10 : ℝ) (12 / 5 : ℝ) ∧
      (16373142251 / 1000000000000 : ℝ) ≤ ∫ t in (23 / 10 : ℝ)..(12 / 5 : ℝ), (((((sigma0 t / ((5 : ℝ) * t) * Real.log (800000000 / 22972653 : ℝ)) + (ind (127 / 50 : ℝ) (3 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) ^ (5 : ℕ) / (22972653 / 781250 : ℝ)))) + (ind (3807 / 2900 : ℝ) (153 / 100 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) / ((19 / 10 : ℝ) * ((253 / 100 : ℝ) - t))))) + (ind (2561 / 1525 : ℝ) (127 / 50 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) / ((36 / 25 : ℝ) * ((177 / 50 : ℝ) - t))))) + (ind (406 / 275 : ℝ) (127 / 50 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) / ((6 / 5 : ℝ) * ((177 / 50 : ℝ) - t))))) :=
  add_int_lb hsum_126 hterm_112 (by norm_num)

private lemma hsum_128 :
    IntervalIntegrable (fun t => (((((sigma0 t / ((5 : ℝ) * t) * Real.log (800000000 / 22972653 : ℝ)) + (ind (127 / 50 : ℝ) (3 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) ^ (5 : ℕ) / (22972653 / 781250 : ℝ)))) + (ind (3807 / 2900 : ℝ) (153 / 100 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) / ((19 / 10 : ℝ) * ((253 / 100 : ℝ) - t))))) + (ind (2561 / 1525 : ℝ) (127 / 50 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) / ((36 / 25 : ℝ) * ((177 / 50 : ℝ) - t))))) + (ind (406 / 275 : ℝ) (127 / 50 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) / ((6 / 5 : ℝ) * ((177 / 50 : ℝ) - t))))) + (ind (153 / 100 : ℝ) (127 / 50 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) ^ (2 : ℕ) / (4807 / 1000 : ℝ)))) volume (23 / 10 : ℝ) (12 / 5 : ℝ) ∧
      (14742200187 / 625000000000 : ℝ) ≤ ∫ t in (23 / 10 : ℝ)..(12 / 5 : ℝ), ((((((sigma0 t / ((5 : ℝ) * t) * Real.log (800000000 / 22972653 : ℝ)) + (ind (127 / 50 : ℝ) (3 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) ^ (5 : ℕ) / (22972653 / 781250 : ℝ)))) + (ind (3807 / 2900 : ℝ) (153 / 100 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) / ((19 / 10 : ℝ) * ((253 / 100 : ℝ) - t))))) + (ind (2561 / 1525 : ℝ) (127 / 50 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) / ((36 / 25 : ℝ) * ((177 / 50 : ℝ) - t))))) + (ind (406 / 275 : ℝ) (127 / 50 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) / ((6 / 5 : ℝ) * ((177 / 50 : ℝ) - t))))) + (ind (153 / 100 : ℝ) (127 / 50 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) ^ (2 : ℕ) / (4807 / 1000 : ℝ)))) :=
  add_int_lb hsum_127 hterm_115 (by norm_num)

private lemma hsum_129 :
    IntervalIntegrable (fun t => ((((((sigma0 t / ((5 : ℝ) * t) * Real.log (800000000 / 22972653 : ℝ)) + (ind (127 / 50 : ℝ) (3 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) ^ (5 : ℕ) / (22972653 / 781250 : ℝ)))) + (ind (3807 / 2900 : ℝ) (153 / 100 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) / ((19 / 10 : ℝ) * ((253 / 100 : ℝ) - t))))) + (ind (2561 / 1525 : ℝ) (127 / 50 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) / ((36 / 25 : ℝ) * ((177 / 50 : ℝ) - t))))) + (ind (406 / 275 : ℝ) (127 / 50 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) / ((6 / 5 : ℝ) * ((177 / 50 : ℝ) - t))))) + (ind (153 / 100 : ℝ) (127 / 50 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) ^ (2 : ℕ) / (4807 / 1000 : ℝ)))) + (ind (750008 / 538325 : ℝ) (2561 / 1525 : ℝ) t / (5 * t * (1 - t / (227 / 50 : ℝ))) * Real.log ((227 / 50 : ℝ) ^ (2 : ℕ) / (((353 / 100 : ℝ) * (227 / 50 : ℝ) - (227 / 50 : ℝ) - (353 / 100 : ℝ) * t) * ((61 / 25 : ℝ) * (227 / 50 : ℝ) - (227 / 50 : ℝ) - (61 / 25 : ℝ) * t))))) volume (23 / 10 : ℝ) (12 / 5 : ℝ) ∧
      (14742200187 / 625000000000 : ℝ) ≤ ∫ t in (23 / 10 : ℝ)..(12 / 5 : ℝ), (((((((sigma0 t / ((5 : ℝ) * t) * Real.log (800000000 / 22972653 : ℝ)) + (ind (127 / 50 : ℝ) (3 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) ^ (5 : ℕ) / (22972653 / 781250 : ℝ)))) + (ind (3807 / 2900 : ℝ) (153 / 100 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) / ((19 / 10 : ℝ) * ((253 / 100 : ℝ) - t))))) + (ind (2561 / 1525 : ℝ) (127 / 50 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) / ((36 / 25 : ℝ) * ((177 / 50 : ℝ) - t))))) + (ind (406 / 275 : ℝ) (127 / 50 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) / ((6 / 5 : ℝ) * ((177 / 50 : ℝ) - t))))) + (ind (153 / 100 : ℝ) (127 / 50 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) ^ (2 : ℕ) / (4807 / 1000 : ℝ)))) + (ind (750008 / 538325 : ℝ) (2561 / 1525 : ℝ) t / (5 * t * (1 - t / (227 / 50 : ℝ))) * Real.log ((227 / 50 : ℝ) ^ (2 : ℕ) / (((353 / 100 : ℝ) * (227 / 50 : ℝ) - (227 / 50 : ℝ) - (353 / 100 : ℝ) * t) * ((61 / 25 : ℝ) * (227 / 50 : ℝ) - (227 / 50 : ℝ) - (61 / 25 : ℝ) * t))))) :=
  add_int_lb hsum_128 hterm_118 (by norm_num)

private lemma hsum_130 :
    IntervalIntegrable (fun t => (((((((sigma0 t / ((5 : ℝ) * t) * Real.log (800000000 / 22972653 : ℝ)) + (ind (127 / 50 : ℝ) (3 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) ^ (5 : ℕ) / (22972653 / 781250 : ℝ)))) + (ind (3807 / 2900 : ℝ) (153 / 100 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) / ((19 / 10 : ℝ) * ((253 / 100 : ℝ) - t))))) + (ind (2561 / 1525 : ℝ) (127 / 50 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) / ((36 / 25 : ℝ) * ((177 / 50 : ℝ) - t))))) + (ind (406 / 275 : ℝ) (127 / 50 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) / ((6 / 5 : ℝ) * ((177 / 50 : ℝ) - t))))) + (ind (153 / 100 : ℝ) (127 / 50 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) ^ (2 : ℕ) / (4807 / 1000 : ℝ)))) + (ind (750008 / 538325 : ℝ) (2561 / 1525 : ℝ) t / (5 * t * (1 - t / (227 / 50 : ℝ))) * Real.log ((227 / 50 : ℝ) ^ (2 : ℕ) / (((353 / 100 : ℝ) * (227 / 50 : ℝ) - (227 / 50 : ℝ) - (353 / 100 : ℝ) * t) * ((61 / 25 : ℝ) * (227 / 50 : ℝ) - (227 / 50 : ℝ) - (61 / 25 : ℝ) * t))))) + (ind (2561 / 1525 : ℝ) (864189 / 511850 : ℝ) t / (5 * t * (1 - t / (227 / 50 : ℝ))) * Real.log ((227 / 50 : ℝ) * ((227 / 50 : ℝ) - 1 - t) / ((353 / 100 : ℝ) * (227 / 50 : ℝ) - (227 / 50 : ℝ) - (353 / 100 : ℝ) * t)))) volume (23 / 10 : ℝ) (12 / 5 : ℝ) ∧
      (14742200187 / 625000000000 : ℝ) ≤ ∫ t in (23 / 10 : ℝ)..(12 / 5 : ℝ), ((((((((sigma0 t / ((5 : ℝ) * t) * Real.log (800000000 / 22972653 : ℝ)) + (ind (127 / 50 : ℝ) (3 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) ^ (5 : ℕ) / (22972653 / 781250 : ℝ)))) + (ind (3807 / 2900 : ℝ) (153 / 100 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) / ((19 / 10 : ℝ) * ((253 / 100 : ℝ) - t))))) + (ind (2561 / 1525 : ℝ) (127 / 50 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) / ((36 / 25 : ℝ) * ((177 / 50 : ℝ) - t))))) + (ind (406 / 275 : ℝ) (127 / 50 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) / ((6 / 5 : ℝ) * ((177 / 50 : ℝ) - t))))) + (ind (153 / 100 : ℝ) (127 / 50 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) ^ (2 : ℕ) / (4807 / 1000 : ℝ)))) + (ind (750008 / 538325 : ℝ) (2561 / 1525 : ℝ) t / (5 * t * (1 - t / (227 / 50 : ℝ))) * Real.log ((227 / 50 : ℝ) ^ (2 : ℕ) / (((353 / 100 : ℝ) * (227 / 50 : ℝ) - (227 / 50 : ℝ) - (353 / 100 : ℝ) * t) * ((61 / 25 : ℝ) * (227 / 50 : ℝ) - (227 / 50 : ℝ) - (61 / 25 : ℝ) * t))))) + (ind (2561 / 1525 : ℝ) (864189 / 511850 : ℝ) t / (5 * t * (1 - t / (227 / 50 : ℝ))) * Real.log ((227 / 50 : ℝ) * ((227 / 50 : ℝ) - 1 - t) / ((353 / 100 : ℝ) * (227 / 50 : ℝ) - (227 / 50 : ℝ) - (353 / 100 : ℝ) * t)))) :=
  add_int_lb hsum_129 hterm_119 (by norm_num)

private lemma hsum_131 :
    IntervalIntegrable (fun t => ((((((((sigma0 t / ((5 : ℝ) * t) * Real.log (800000000 / 22972653 : ℝ)) + (ind (127 / 50 : ℝ) (3 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) ^ (5 : ℕ) / (22972653 / 781250 : ℝ)))) + (ind (3807 / 2900 : ℝ) (153 / 100 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) / ((19 / 10 : ℝ) * ((253 / 100 : ℝ) - t))))) + (ind (2561 / 1525 : ℝ) (127 / 50 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) / ((36 / 25 : ℝ) * ((177 / 50 : ℝ) - t))))) + (ind (406 / 275 : ℝ) (127 / 50 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) / ((6 / 5 : ℝ) * ((177 / 50 : ℝ) - t))))) + (ind (153 / 100 : ℝ) (127 / 50 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) ^ (2 : ℕ) / (4807 / 1000 : ℝ)))) + (ind (750008 / 538325 : ℝ) (2561 / 1525 : ℝ) t / (5 * t * (1 - t / (227 / 50 : ℝ))) * Real.log ((227 / 50 : ℝ) ^ (2 : ℕ) / (((353 / 100 : ℝ) * (227 / 50 : ℝ) - (227 / 50 : ℝ) - (353 / 100 : ℝ) * t) * ((61 / 25 : ℝ) * (227 / 50 : ℝ) - (227 / 50 : ℝ) - (61 / 25 : ℝ) * t))))) + (ind (2561 / 1525 : ℝ) (864189 / 511850 : ℝ) t / (5 * t * (1 - t / (227 / 50 : ℝ))) * Real.log ((227 / 50 : ℝ) * ((227 / 50 : ℝ) - 1 - t) / ((353 / 100 : ℝ) * (227 / 50 : ℝ) - (227 / 50 : ℝ) - (353 / 100 : ℝ) * t)))) + (ind (2043 / 1450 : ℝ) (864189 / 511850 : ℝ) t / (5 * t * (1 - t / (227 / 50 : ℝ))) * Real.log ((227 / 50 : ℝ) / ((29 / 10 : ℝ) * (227 / 50 : ℝ) - (227 / 50 : ℝ) - (29 / 10 : ℝ) * t)))) volume (23 / 10 : ℝ) (12 / 5 : ℝ) ∧
      (14742200187 / 625000000000 : ℝ) ≤ ∫ t in (23 / 10 : ℝ)..(12 / 5 : ℝ), (((((((((sigma0 t / ((5 : ℝ) * t) * Real.log (800000000 / 22972653 : ℝ)) + (ind (127 / 50 : ℝ) (3 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) ^ (5 : ℕ) / (22972653 / 781250 : ℝ)))) + (ind (3807 / 2900 : ℝ) (153 / 100 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) / ((19 / 10 : ℝ) * ((253 / 100 : ℝ) - t))))) + (ind (2561 / 1525 : ℝ) (127 / 50 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) / ((36 / 25 : ℝ) * ((177 / 50 : ℝ) - t))))) + (ind (406 / 275 : ℝ) (127 / 50 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) / ((6 / 5 : ℝ) * ((177 / 50 : ℝ) - t))))) + (ind (153 / 100 : ℝ) (127 / 50 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) ^ (2 : ℕ) / (4807 / 1000 : ℝ)))) + (ind (750008 / 538325 : ℝ) (2561 / 1525 : ℝ) t / (5 * t * (1 - t / (227 / 50 : ℝ))) * Real.log ((227 / 50 : ℝ) ^ (2 : ℕ) / (((353 / 100 : ℝ) * (227 / 50 : ℝ) - (227 / 50 : ℝ) - (353 / 100 : ℝ) * t) * ((61 / 25 : ℝ) * (227 / 50 : ℝ) - (227 / 50 : ℝ) - (61 / 25 : ℝ) * t))))) + (ind (2561 / 1525 : ℝ) (864189 / 511850 : ℝ) t / (5 * t * (1 - t / (227 / 50 : ℝ))) * Real.log ((227 / 50 : ℝ) * ((227 / 50 : ℝ) - 1 - t) / ((353 / 100 : ℝ) * (227 / 50 : ℝ) - (227 / 50 : ℝ) - (353 / 100 : ℝ) * t)))) + (ind (2043 / 1450 : ℝ) (864189 / 511850 : ℝ) t / (5 * t * (1 - t / (227 / 50 : ℝ))) * Real.log ((227 / 50 : ℝ) / ((29 / 10 : ℝ) * (227 / 50 : ℝ) - (227 / 50 : ℝ) - (29 / 10 : ℝ) * t)))) :=
  add_int_lb hsum_130 hterm_120 (by norm_num)

private lemma hsum_132 :
    IntervalIntegrable (fun t => (((((((((sigma0 t / ((5 : ℝ) * t) * Real.log (800000000 / 22972653 : ℝ)) + (ind (127 / 50 : ℝ) (3 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) ^ (5 : ℕ) / (22972653 / 781250 : ℝ)))) + (ind (3807 / 2900 : ℝ) (153 / 100 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) / ((19 / 10 : ℝ) * ((253 / 100 : ℝ) - t))))) + (ind (2561 / 1525 : ℝ) (127 / 50 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) / ((36 / 25 : ℝ) * ((177 / 50 : ℝ) - t))))) + (ind (406 / 275 : ℝ) (127 / 50 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) / ((6 / 5 : ℝ) * ((177 / 50 : ℝ) - t))))) + (ind (153 / 100 : ℝ) (127 / 50 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) ^ (2 : ℕ) / (4807 / 1000 : ℝ)))) + (ind (750008 / 538325 : ℝ) (2561 / 1525 : ℝ) t / (5 * t * (1 - t / (227 / 50 : ℝ))) * Real.log ((227 / 50 : ℝ) ^ (2 : ℕ) / (((353 / 100 : ℝ) * (227 / 50 : ℝ) - (227 / 50 : ℝ) - (353 / 100 : ℝ) * t) * ((61 / 25 : ℝ) * (227 / 50 : ℝ) - (227 / 50 : ℝ) - (61 / 25 : ℝ) * t))))) + (ind (2561 / 1525 : ℝ) (864189 / 511850 : ℝ) t / (5 * t * (1 - t / (227 / 50 : ℝ))) * Real.log ((227 / 50 : ℝ) * ((227 / 50 : ℝ) - 1 - t) / ((353 / 100 : ℝ) * (227 / 50 : ℝ) - (227 / 50 : ℝ) - (353 / 100 : ℝ) * t)))) + (ind (2043 / 1450 : ℝ) (864189 / 511850 : ℝ) t / (5 * t * (1 - t / (227 / 50 : ℝ))) * Real.log ((227 / 50 : ℝ) / ((29 / 10 : ℝ) * (227 / 50 : ℝ) - (227 / 50 : ℝ) - (29 / 10 : ℝ) * t)))) + (ind (864189 / 511850 : ℝ) (127 / 50 : ℝ) t / (5 * t * (1 - t / (227 / 50 : ℝ))) * Real.log ((227 / 50 : ℝ) - 1 - t))) volume (23 / 10 : ℝ) (12 / 5 : ℝ) ∧
      (266515082253 / 10000000000000 : ℝ) ≤ ∫ t in (23 / 10 : ℝ)..(12 / 5 : ℝ), ((((((((((sigma0 t / ((5 : ℝ) * t) * Real.log (800000000 / 22972653 : ℝ)) + (ind (127 / 50 : ℝ) (3 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) ^ (5 : ℕ) / (22972653 / 781250 : ℝ)))) + (ind (3807 / 2900 : ℝ) (153 / 100 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) / ((19 / 10 : ℝ) * ((253 / 100 : ℝ) - t))))) + (ind (2561 / 1525 : ℝ) (127 / 50 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) / ((36 / 25 : ℝ) * ((177 / 50 : ℝ) - t))))) + (ind (406 / 275 : ℝ) (127 / 50 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) / ((6 / 5 : ℝ) * ((177 / 50 : ℝ) - t))))) + (ind (153 / 100 : ℝ) (127 / 50 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) ^ (2 : ℕ) / (4807 / 1000 : ℝ)))) + (ind (750008 / 538325 : ℝ) (2561 / 1525 : ℝ) t / (5 * t * (1 - t / (227 / 50 : ℝ))) * Real.log ((227 / 50 : ℝ) ^ (2 : ℕ) / (((353 / 100 : ℝ) * (227 / 50 : ℝ) - (227 / 50 : ℝ) - (353 / 100 : ℝ) * t) * ((61 / 25 : ℝ) * (227 / 50 : ℝ) - (227 / 50 : ℝ) - (61 / 25 : ℝ) * t))))) + (ind (2561 / 1525 : ℝ) (864189 / 511850 : ℝ) t / (5 * t * (1 - t / (227 / 50 : ℝ))) * Real.log ((227 / 50 : ℝ) * ((227 / 50 : ℝ) - 1 - t) / ((353 / 100 : ℝ) * (227 / 50 : ℝ) - (227 / 50 : ℝ) - (353 / 100 : ℝ) * t)))) + (ind (2043 / 1450 : ℝ) (864189 / 511850 : ℝ) t / (5 * t * (1 - t / (227 / 50 : ℝ))) * Real.log ((227 / 50 : ℝ) / ((29 / 10 : ℝ) * (227 / 50 : ℝ) - (227 / 50 : ℝ) - (29 / 10 : ℝ) * t)))) + (ind (864189 / 511850 : ℝ) (127 / 50 : ℝ) t / (5 * t * (1 - t / (227 / 50 : ℝ))) * Real.log ((227 / 50 : ℝ) - 1 - t))) :=
  add_int_lb hsum_131 hterm_121 (by norm_num)


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



theorem main_thm : (candidateMatrixQ 0 2 : ℝ) ≤ integralMatrix 0 2 := by
  have hcand : (candidateMatrixQ 0 2 : ℝ) = (53303 / 2000000 : ℝ) := by simp [candidateMatrixQ]; try norm_num
  have hga : grid ⟨(2 : Fin 9).val, by omega⟩ = (23 / 10 : ℝ) := by simp [grid]; try norm_num
  have hgb : grid ⟨(2 : Fin 9).val + 1, by omega⟩ = (12 / 5 : ℝ) := by simp [grid]; try norm_num
  unfold integralMatrix
  rw [hcand, hga, hgb]
  have hint_eq : (∫ t in (23 / 10 : ℝ)..(12 / 5 : ℝ), tableKernel 0 t) =
      ∫ t in (23 / 10 : ℝ)..(12 / 5 : ℝ), ((((((((((sigma0 t / ((5 : ℝ) * t) * Real.log (800000000 / 22972653 : ℝ)) + (ind (127 / 50 : ℝ) (3 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) ^ (5 : ℕ) / (22972653 / 781250 : ℝ)))) + (ind (3807 / 2900 : ℝ) (153 / 100 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) / ((19 / 10 : ℝ) * ((253 / 100 : ℝ) - t))))) + (ind (2561 / 1525 : ℝ) (127 / 50 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) / ((36 / 25 : ℝ) * ((177 / 50 : ℝ) - t))))) + (ind (406 / 275 : ℝ) (127 / 50 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) / ((6 / 5 : ℝ) * ((177 / 50 : ℝ) - t))))) + (ind (153 / 100 : ℝ) (127 / 50 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) ^ (2 : ℕ) / (4807 / 1000 : ℝ)))) + (ind (750008 / 538325 : ℝ) (2561 / 1525 : ℝ) t / (5 * t * (1 - t / (227 / 50 : ℝ))) * Real.log ((227 / 50 : ℝ) ^ (2 : ℕ) / (((353 / 100 : ℝ) * (227 / 50 : ℝ) - (227 / 50 : ℝ) - (353 / 100 : ℝ) * t) * ((61 / 25 : ℝ) * (227 / 50 : ℝ) - (227 / 50 : ℝ) - (61 / 25 : ℝ) * t))))) + (ind (2561 / 1525 : ℝ) (864189 / 511850 : ℝ) t / (5 * t * (1 - t / (227 / 50 : ℝ))) * Real.log ((227 / 50 : ℝ) * ((227 / 50 : ℝ) - 1 - t) / ((353 / 100 : ℝ) * (227 / 50 : ℝ) - (227 / 50 : ℝ) - (353 / 100 : ℝ) * t)))) + (ind (2043 / 1450 : ℝ) (864189 / 511850 : ℝ) t / (5 * t * (1 - t / (227 / 50 : ℝ))) * Real.log ((227 / 50 : ℝ) / ((29 / 10 : ℝ) * (227 / 50 : ℝ) - (227 / 50 : ℝ) - (29 / 10 : ℝ) * t)))) + (ind (864189 / 511850 : ℝ) (127 / 50 : ℝ) t / (5 * t * (1 - t / (227 / 50 : ℝ))) * Real.log ((227 / 50 : ℝ) - 1 - t))) := by
    apply integral_congr; intro t _; exact hkern_eq t
  rw [hint_eq]
  exact le_trans (by norm_num) hsum_132.2

end
end W5Cert_R1_entry_0_2

theorem solution : (candidateMatrixQ 0 2 : ℝ) ≤ integralMatrix 0 2 :=
  W5Cert_R1_entry_0_2.main_thm
