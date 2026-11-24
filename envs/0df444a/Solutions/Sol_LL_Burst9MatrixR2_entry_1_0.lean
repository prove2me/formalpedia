-- Prove2me | solution 1 for LL_Burst9MatrixR2.entry_1_0
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-24T01:15:39.698475+00:00
-- url     : https://prove2.me/submissions/03dced5c-6a2e-453e-9e54-9d4d5e6fe295

import Definitions.Def_LL_Burst9MatrixR2_candidateMatrixQ
import Definitions.Def_LL_Burst9MatrixR2_integralMatrix

open Real Set intervalIntegral Filter MeasureTheory
open scoped Topology
open LL_Burst9MatrixR2

namespace W5Cert_R2_entry_1_0
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
    have h3 : HasDerivAt (fun w : ℝ => 2 * (w + w ^ 3 / 3 + w ^ 5 / 5 + w ^ 7 / 7))
        (2 * (1 + w ^ 2 + w ^ 4 + w ^ 6)) w := by
      have hp3 : HasDerivAt (fun w : ℝ => w ^ 3 / 3) (w ^ 2) w :=
        ((hasDerivAt_pow 3 w).div_const 3).congr_deriv (by ring)
      have hp5 : HasDerivAt (fun w : ℝ => w ^ 5 / 5) (w ^ 4) w :=
        ((hasDerivAt_pow 5 w).div_const 5).congr_deriv (by ring)
      have hp7 : HasDerivAt (fun w : ℝ => w ^ 7 / 7) (w ^ 6) w :=
        ((hasDerivAt_pow 7 w).div_const 7).congr_deriv (by ring)
      simpa using ((((hasDerivAt_id w).add hp3).add hp5).add hp7).const_mul 2
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
    (h_arith : 0 ≤ y ∧ y < 1 ∧
      M * (1 - y) = (2 : ℝ) ^ e2 * (3 : ℝ) ^ e3 * (5 : ℝ) ^ e5 * (1 + y) ∧
      lo ≤ min (e2 * LOG2_LO) (e2 * LOG2_HI) + min (e3 * LOG3_LO) (e3 * LOG3_HI) +
        min (e5 * LOG5_LO) (e5 * LOG5_HI) + 2 * (y + y ^ 3 / 3 + y ^ 5 / 5) ∧
      max (e2 * LOG2_LO) (e2 * LOG2_HI) + max (e3 * LOG3_LO) (e3 * LOG3_HI) +
        max (e5 * LOG5_LO) (e5 * LOG5_HI) +
        2 * (y + y ^ 3 / 3 + y ^ 5 / 5) + 2 * y ^ 7 / (7 * (1 - y ^ 2)) ≤ hi) :
    lo ≤ Real.log M ∧ Real.log M ≤ hi := by
  rcases h_arith with ⟨hy0, hy1, hM, hlo, hhi⟩
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

private lemma continuous_centered_poly6 (a0 a1 a2 a3 a4 a5 a6 m : ℝ) :
    Continuous (fun t => a0 + a1 * (t - m) + a2 * (t - m) ^ 2 + a3 * (t - m) ^ 3 +
      a4 * (t - m) ^ 4 + a5 * (t - m) ^ 5 + a6 * (t - m) ^ 6) := by fun_prop

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
    (continuous_centered_poly6 c0 c1 c2 c3 c4 c5 c6 m).intervalIntegrable u v
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
    (hL : L_lo ≤ Real.log M ∧ Real.log M ≤ L_hi)
    (h_arith : u ≤ v ∧ m = (u + v) / 2 ∧ h = (v - u) / 2 ∧
      M = A + B * m ∧ N = C + D * m ∧ B = M * b ∧ D = N * d ∧
      0 < M ∧ 0 < N ∧ 0 ≤ K ∧ |b| ≤ K ∧ |d| ≤ K ∧ K * h ≤ 1 / 10 ∧
      out_lo ≤ quadLogLo h b d K L_lo N ∧ quadLogHi h b d K L_hi N ≤ out_hi) :
    IntervalIntegrable (fun t => Real.log (A + B * t) / (C + D * t)) volume u v ∧
      out_lo ≤ ∫ t in u..v, Real.log (A + B * t) / (C + D * t) ∧
      ∫ t in u..v, Real.log (A + B * t) / (C + D * t) ≤ out_hi := by
  rcases h_arith with ⟨huv, hm, hh, hM_eq, hN_eq, hb_eq, hd_eq, hM, hN, hK0, hb_le, hd_le, hKh, hout_lo, hout_hi⟩
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
      apply integral_mono_on huv ((continuous_centered_poly6 1 (-d) (d ^ 2) (-d ^ 3) (d ^ 4) (-d ^ 5) 0 m).intervalIntegrable u v) hg1_int
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
      apply integral_mono_on huv hg1_int ((continuous_centered_poly6 1 (-d) (d ^ 2) (-d ^ 3) (d ^ 4) (-d ^ 5) (10 / 9 * d ^ 6) m).intervalIntegrable u v)
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
          (Real.log (1 + b * (t - m)) - (1 + d * (t - m)) * r_mid t) / (1 + d * (t - m)) :=
        div_sub' hd_pos.ne'
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
      apply integral_mono_on huv ((continuous_centered_poly6 0 b (-(b ^ 2 / 2 + b * d))
        (b ^ 3 / 3 + b ^ 2 * d / 2 + b * d ^ 2)
        (-(b ^ 4 / 4 + b ^ 3 * d / 3 + b ^ 2 * d ^ 2 / 2 + b * d ^ 3))
        (b ^ 5 / 5 + b ^ 4 * d / 4 + b ^ 3 * d ^ 2 / 3 + b ^ 2 * d ^ 3 / 2 + b * d ^ 4)
        (-3 * K ^ 6) m).intervalIntegrable u v) hg2_int
      intro t ht
      have h1 := (abs_le.mp (hg2_pt t ht)).1
      change r_mid t + (-3 * K ^ 6) * (t - m) ^ 6 ≤ g2 t
      linarith
    have hm_hi : ∫ t in u..v, g2 t ≤ ∫ t in u..v, r_hi_fn t := by
      apply integral_mono_on huv hg2_int ((continuous_centered_poly6 0 b (-(b ^ 2 / 2 + b * d))
        (b ^ 3 / 3 + b ^ 2 * d / 2 + b * d ^ 2)
        (-(b ^ 4 / 4 + b ^ 3 * d / 3 + b ^ 2 * d ^ 2 / 2 + b * d ^ 3))
        (b ^ 5 / 5 + b ^ 4 * d / 4 + b ^ 3 * d ^ 2 / 3 + b ^ 2 * d ^ 3 / 2 + b * d ^ 4)
        (3 * K ^ 6) m).intervalIntegrable u v)
      intro t ht
      have h2 := (abs_le.mp (hg2_pt t ht)).2
      change g2 t ≤ r_mid t + (3 * K ^ 6) * (t - m) ^ 6
      linarith
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

def quadProd5Lo (m h b1 c0 c2 c4 E6 Alo Ahi Blo Bhi : ℝ) : ℝ :=
  (2 * h * c0 + 2 / 3 * h ^ 3 * c2 + 2 / 5 * h ^ 5 * c4 -
    6 * h * ((Ahi - Alo) + (Bhi - Blo)) -
    2 / 7 * (2 * E6 + b1 ^ 6) * h ^ 7) / (m + 1)

private lemma quad_prod5_tele_err (x h b1 b2 d c0 c1 c2 c3 c4 c5 e6 e7 e8 e9 e10 E6 Alo Blo : ℝ)
    (hxh : |x| ≤ h)
    (hc0 : c0 = Alo * Blo)
    (hc1 : c1 = Alo * b2 - Blo * b1 - d * c0)
    (hc2 : c2 = -Alo * b2 ^ 2 / 2 + Blo * b1 ^ 2 / 2 - b1 * b2 - d * c1)
    (hc3 : c3 = Alo * b2 ^ 3 / 3 - Blo * b1 ^ 3 / 3 + b1 * b2 ^ 2 / 2 + b1 ^ 2 * b2 / 2 - d * c2)
    (hc4 : c4 = -Alo * b2 ^ 4 / 4 + Blo * b1 ^ 4 / 4 - b1 * b2 ^ 3 / 3 - b1 ^ 2 * b2 ^ 2 / 4 - b1 ^ 3 * b2 / 3 - d * c3)
    (hc5 : c5 = Alo * b2 ^ 5 / 5 - Blo * b1 ^ 5 / 5 + b1 * b2 ^ 4 / 4 + b1 ^ 2 * b2 ^ 3 / 6 + b1 ^ 3 * b2 ^ 2 / 6 + b1 ^ 4 * b2 / 4 - d * c4)
    (he6 : e6 = d * c5 + b1 * b2 ^ 5 / 5 + b1 ^ 2 * b2 ^ 4 / 8 + b1 ^ 3 * b2 ^ 3 / 9 + b1 ^ 4 * b2 ^ 2 / 8 + b1 ^ 5 * b2 / 5)
    (he7 : e7 = -b1 ^ 2 * b2 ^ 5 / 10 - b1 ^ 3 * b2 ^ 4 / 12 - b1 ^ 4 * b2 ^ 3 / 12 - b1 ^ 5 * b2 ^ 2 / 10)
    (he8 : e8 = b1 ^ 3 * b2 ^ 5 / 15 + b1 ^ 4 * b2 ^ 4 / 16 + b1 ^ 5 * b2 ^ 3 / 15)
    (he9 : e9 = -b1 ^ 4 * b2 ^ 5 / 20 - b1 ^ 5 * b2 ^ 4 / 20)
    (he10 : e10 = b1 ^ 5 * b2 ^ 5 / 25)
    (hE6 : |e6| + |e7| * h + |e8| * h ^ 2 + |e9| * h ^ 3 + |e10| * h ^ 4 ≤ E6) :
    |(1 + d * x) * (c0 + c1 * x + c2 * x ^ 2 + c3 * x ^ 3 + c4 * x ^ 4 + c5 * x ^ 5) -
      (Alo - (b1 * x - (b1 * x) ^ 2 / 2 + (b1 * x) ^ 3 / 3 - (b1 * x) ^ 4 / 4 + (b1 * x) ^ 5 / 5)) *
        (Blo + (b2 * x - (b2 * x) ^ 2 / 2 + (b2 * x) ^ 3 / 3 - (b2 * x) ^ 4 / 4 + (b2 * x) ^ 5 / 5))| ≤
      E6 * x ^ 6 := by
  have hx6 : 0 ≤ x ^ 6 := by positivity
  have htele : (1 + d * x) * (c0 + c1 * x + c2 * x ^ 2 + c3 * x ^ 3 + c4 * x ^ 4 + c5 * x ^ 5) -
      (Alo - (b1 * x - (b1 * x) ^ 2 / 2 + (b1 * x) ^ 3 / 3 - (b1 * x) ^ 4 / 4 + (b1 * x) ^ 5 / 5)) *
        (Blo + (b2 * x - (b2 * x) ^ 2 / 2 + (b2 * x) ^ 3 / 3 - (b2 * x) ^ 4 / 4 + (b2 * x) ^ 5 / 5)) =
      (e6 + e7 * x + e8 * x ^ 2 + e9 * x ^ 3 + e10 * x ^ 4) * x ^ 6 := by
    rw [he6, he7, he8, he9, he10, hc5, hc4, hc3, hc2, hc1, hc0]; ring
  rw [htele, abs_mul, abs_of_nonneg hx6]
  apply mul_le_mul_of_nonneg_right _ hx6
  have ht1 := abs_add_le (e6 + e7 * x + e8 * x ^ 2 + e9 * x ^ 3) (e10 * x ^ 4)
  have ht2 := abs_add_le (e6 + e7 * x + e8 * x ^ 2) (e9 * x ^ 3)
  have ht3 := abs_add_le (e6 + e7 * x) (e8 * x ^ 2)
  have ht4 := abs_add_le e6 (e7 * x)
  have hp1 : |e7 * x| ≤ |e7| * h := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left hxh (abs_nonneg _)
  have hp2 : |e8 * x ^ 2| ≤ |e8| * h ^ 2 := by
    rw [abs_mul, abs_pow]
    have : |x| ^ 2 ≤ h ^ 2 := by have := abs_nonneg x; gcongr
    exact mul_le_mul_of_nonneg_left this (abs_nonneg _)
  have hp3 : |e9 * x ^ 3| ≤ |e9| * h ^ 3 := by
    rw [abs_mul, abs_pow]
    have : |x| ^ 3 ≤ h ^ 3 := by have := abs_nonneg x; gcongr
    exact mul_le_mul_of_nonneg_left this (abs_nonneg _)
  have hp4 : |e10 * x ^ 4| ≤ |e10| * h ^ 4 := by
    rw [abs_mul, abs_pow]
    have : |x| ^ 4 ≤ h ^ 4 := by have := abs_nonneg x; gcongr
    exact mul_le_mul_of_nonneg_left this (abs_nonneg _)
  linarith only [ht1, ht2, ht3, ht4, hp1, hp2, hp3, hp4, hE6]

private lemma quad_prod5_pt_lb (gb m h t b1 b2 d c0 c1 c2 c3 c4 c5 e6 e7 e8 e9 e10 E6 Alo Ahi Blo Bhi : ℝ)
    (hm1 : 1 ≤ m) (hgb : 0 < gb) (hE6_nn : 0 ≤ E6)
    (hb1_pos : 0 < b1) (hb2_pos : 0 < b2) (hb2_le1 : b2 ≤ b1)
    (ht_id : t = m * (1 + b1 * (t - m)))
    (ht2_id : (t + 2) / 3 = ((m + 2) / 3) * (1 + b2 * (t - m)))
    (ht1_id : t + 1 = (1 + d * (t - m)) * (m + 1))
    (htm : |t - m| ≤ h)
    (hx1 : |b1 * (t - m)| ≤ 1 / 10) (hx2 : |b2 * (t - m)| ≤ 1 / 10)
    (hd1 : 9 / 10 ≤ 1 + d * (t - m)) (hb1_1 : 9 / 10 ≤ 1 + b1 * (t - m)) (hb2_1 : 9 / 10 ≤ 1 + b2 * (t - m))
    (hc0 : c0 = Alo * Blo)
    (hc1 : c1 = Alo * b2 - Blo * b1 - d * c0)
    (hc2 : c2 = -Alo * b2 ^ 2 / 2 + Blo * b1 ^ 2 / 2 - b1 * b2 - d * c1)
    (hc3 : c3 = Alo * b2 ^ 3 / 3 - Blo * b1 ^ 3 / 3 + b1 * b2 ^ 2 / 2 + b1 ^ 2 * b2 / 2 - d * c2)
    (hc4 : c4 = -Alo * b2 ^ 4 / 4 + Blo * b1 ^ 4 / 4 - b1 * b2 ^ 3 / 3 - b1 ^ 2 * b2 ^ 2 / 4 - b1 ^ 3 * b2 / 3 - d * c3)
    (hc5 : c5 = Alo * b2 ^ 5 / 5 - Blo * b1 ^ 5 / 5 + b1 * b2 ^ 4 / 4 + b1 ^ 2 * b2 ^ 3 / 6 + b1 ^ 3 * b2 ^ 2 / 6 + b1 ^ 4 * b2 / 4 - d * c4)
    (he6 : e6 = d * c5 + b1 * b2 ^ 5 / 5 + b1 ^ 2 * b2 ^ 4 / 8 + b1 ^ 3 * b2 ^ 3 / 9 + b1 ^ 4 * b2 ^ 2 / 8 + b1 ^ 5 * b2 / 5)
    (he7 : e7 = -b1 ^ 2 * b2 ^ 5 / 10 - b1 ^ 3 * b2 ^ 4 / 12 - b1 ^ 4 * b2 ^ 3 / 12 - b1 ^ 5 * b2 ^ 2 / 10)
    (he8 : e8 = b1 ^ 3 * b2 ^ 5 / 15 + b1 ^ 4 * b2 ^ 4 / 16 + b1 ^ 5 * b2 ^ 3 / 15)
    (he9 : e9 = -b1 ^ 4 * b2 ^ 5 / 20 - b1 ^ 5 * b2 ^ 4 / 20)
    (he10 : e10 = b1 ^ 5 * b2 ^ 5 / 25)
    (hE6 : |e6| + |e7| * h + |e8| * h ^ 2 + |e9| * h ^ 3 + |e10| * h ^ 4 ≤ E6)
    (hA_range : -1 / 10 ≤ Alo ∧ Alo ≤ 3 / 2 ∧ Ahi - Alo ≤ 1 / 100)
    (hB_range : 0 ≤ Blo ∧ Blo ≤ 1 ∧ Bhi - Blo ≤ 1 / 100)
    (hA : Alo ≤ Real.log (gb / m) ∧ Real.log (gb / m) ≤ Ahi)
    (hB : Blo ≤ Real.log ((m + 2) / 3) ∧ Real.log ((m + 2) / 3) ≤ Bhi) :
    ((c0 - 3 * ((Ahi - Alo) + (Bhi - Blo))) + c1 * (t - m) + c2 * (t - m) ^ 2 +
      c3 * (t - m) ^ 3 + c4 * (t - m) ^ 4 + c5 * (t - m) ^ 5 +
      (-(2 * E6 + b1 ^ 6)) * (t - m) ^ 6) / (m + 1) ≤
      Real.log (gb / t) * Real.log ((t + 2) / 3) / (t + 1) := by
  have hm_pos : 0 < m := by linarith only [hm1]
  have hm1_pos : 0 < m + 1 := by linarith only [hm1]
  have hd_pos : 0 < 1 + d * (t - m) := by linarith only [hd1]
  have hgbt_eq : gb / t = (gb / m) / (1 + b1 * (t - m)) := by
    conv_lhs => rw [ht_id]
    rw [div_mul_eq_div_div]
  have ha_val : Real.log (gb / t) = Real.log (gb / m) - Real.log (1 + b1 * (t - m)) := by
    rw [hgbt_eq, Real.log_div (div_pos hgb hm_pos).ne' (by linarith only [hb1_1])]
  have hb_val : Real.log ((t + 2) / 3) = Real.log ((m + 2) / 3) + Real.log (1 + b2 * (t - m)) := by
    rw [ht2_id, Real.log_mul (by positivity) (by linarith only [hb2_1])]
  have hp5_1 := abs_log_one_add_sub_P5 (b1 * (t - m)) hx1
  have hp5_2 := abs_log_one_add_sub_P5 (b2 * (t - m)) hx2
  have hb2x6 : (b2 * (t - m)) ^ 6 ≤ b1 ^ 6 * (t - m) ^ 6 := by
    have hx6 : 0 ≤ (t - m) ^ 6 := by positivity
    have hb26 : b2 ^ 6 ≤ b1 ^ 6 := by gcongr
    calc (b2 * (t - m)) ^ 6 = b2 ^ 6 * (t - m) ^ 6 := mul_pow b2 (t - m) 6
      _ ≤ b1 ^ 6 * (t - m) ^ 6 := mul_le_mul_of_nonneg_right hb26 hx6
  let pa := Alo - (b1 * (t - m) - (b1 * (t - m)) ^ 2 / 2 + (b1 * (t - m)) ^ 3 / 3 -
    (b1 * (t - m)) ^ 4 / 4 + (b1 * (t - m)) ^ 5 / 5)
  let pb := Blo + (b2 * (t - m) - (b2 * (t - m)) ^ 2 / 2 + (b2 * (t - m)) ^ 3 / 3 -
    (b2 * (t - m)) ^ 4 / 4 + (b2 * (t - m)) ^ 5 / 5)
  have ha_err : |Real.log (gb / t) - pa| ≤ (Ahi - Alo) + 5 / 27 * b1 ^ 6 * (t - m) ^ 6 := by
    rw [ha_val]
    obtain ⟨p1, p2⟩ := abs_le.mp hp5_1
    have hbx6 : (b1 * (t - m)) ^ 6 = b1 ^ 6 * (t - m) ^ 6 := mul_pow b1 (t - m) 6
    dsimp only [pa]
    rw [abs_le]; constructor <;> linarith only [p1, p2, hbx6, hA.1, hA.2]
  have hb_err : |Real.log ((t + 2) / 3) - pb| ≤ (Bhi - Blo) + 5 / 27 * b1 ^ 6 * (t - m) ^ 6 := by
    rw [hb_val]
    obtain ⟨p1, p2⟩ := abs_le.mp hp5_2
    dsimp only [pb]
    rw [abs_le]; constructor <;> linarith only [p1, p2, hb2x6, hB.1, hB.2]
  have hpa_abs : |pa| ≤ 2 := by
    obtain ⟨l1, u1⟩ := abs_le.mp hx1
    have h_p5 : |(b1 * (t - m)) - (b1 * (t - m)) ^ 2 / 2 + (b1 * (t - m)) ^ 3 / 3 -
        (b1 * (t - m)) ^ 4 / 4 + (b1 * (t - m)) ^ 5 / 5| ≤ 1 / 2 := by
      have hsq : (b1 * (t - m)) ^ 2 ≤ 1 / 100 := by nlinarith only [l1, u1]
      have hsq0 : 0 ≤ (b1 * (t - m)) ^ 2 := sq_nonneg _
      have h4 : (b1 * (t - m)) ^ 4 ≤ 1 / 10000 := by nlinarith only [hsq, hsq0]
      have h40 : 0 ≤ (b1 * (t - m)) ^ 4 := by positivity
      have h5a : (b1 * (t - m)) ^ 5 = (b1 * (t - m)) ^ 4 * (b1 * (t - m)) := by ring
      have h3a : (b1 * (t - m)) ^ 3 = (b1 * (t - m)) ^ 2 * (b1 * (t - m)) := by ring
      rw [abs_le]; constructor <;> nlinarith only [l1, u1, hsq, hsq0, h4, h40, h5a, h3a]
    obtain ⟨q1, q2⟩ := abs_le.mp h_p5
    dsimp only [pa]
    rw [abs_le]; constructor <;> linarith only [q1, q2, hA_range.1, hA_range.2.1]
  have hpb_abs : |pb| ≤ 6 / 5 := by
    obtain ⟨l2, u2⟩ := abs_le.mp hx2
    have h_p5 : |(b2 * (t - m)) - (b2 * (t - m)) ^ 2 / 2 + (b2 * (t - m)) ^ 3 / 3 -
        (b2 * (t - m)) ^ 4 / 4 + (b2 * (t - m)) ^ 5 / 5| ≤ 1 / 5 := by
      have hsq : (b2 * (t - m)) ^ 2 ≤ 1 / 100 := by nlinarith only [l2, u2]
      have hsq0 : 0 ≤ (b2 * (t - m)) ^ 2 := sq_nonneg _
      have h4 : (b2 * (t - m)) ^ 4 ≤ 1 / 10000 := by nlinarith only [hsq, hsq0]
      have h40 : 0 ≤ (b2 * (t - m)) ^ 4 := by positivity
      have h5a : (b2 * (t - m)) ^ 5 = (b2 * (t - m)) ^ 4 * (b2 * (t - m)) := by ring
      have h3a : (b2 * (t - m)) ^ 3 = (b2 * (t - m)) ^ 2 * (b2 * (t - m)) := by ring
      rw [abs_le]; constructor <;> nlinarith only [l2, u2, hsq, hsq0, h4, h40, h5a, h3a]
    obtain ⟨q1, q2⟩ := abs_le.mp h_p5
    dsimp only [pb]
    rw [abs_le]; constructor <;> linarith only [q1, q2, hB_range.1, hB_range.2.1]
  have hb_abs : |Real.log ((t + 2) / 3)| ≤ 5 / 4 := by
    have hx6_le : (b1 * (t - m)) ^ 6 ≤ 1 / 1000000 := by
      obtain ⟨l1, u1⟩ := abs_le.mp hx1
      have hsq : (b1 * (t - m)) ^ 2 ≤ 1 / 100 := by nlinarith only [l1, u1]
      have hsq0 : 0 ≤ (b1 * (t - m)) ^ 2 := sq_nonneg _
      have h4 : (b1 * (t - m)) ^ 4 ≤ 1 / 10000 := by nlinarith only [hsq, hsq0]
      have h40 : 0 ≤ (b1 * (t - m)) ^ 4 := by positivity
      have h6a : (b1 * (t - m)) ^ 6 = (b1 * (t - m)) ^ 4 * (b1 * (t - m)) ^ 2 := by ring
      nlinarith only [hsq, hsq0, h4, h40, h6a]
    have heq6 := mul_pow b1 (t - m) 6
    have hbx6 : b1 ^ 6 * (t - m) ^ 6 ≤ 1 / 1000000 := by linarith only [hx6_le, heq6]
    obtain ⟨e1, e2⟩ := abs_le.mp hb_err
    obtain ⟨p1, p2⟩ := abs_le.mp hpb_abs
    have hr2 := hB_range.2.2
    rw [abs_le]; constructor <;> linarith only [e1, e2, p1, p2, hbx6, hr2]
  have hepsA : 0 ≤ Ahi - Alo := by linarith only [hA.1, hA.2]
  have hepsB : 0 ≤ Bhi - Blo := by linarith only [hB.1, hB.2]
  have hx6_pos : 0 ≤ (t - m) ^ 6 := by positivity
  have hb6x6_pos : 0 ≤ b1 ^ 6 * (t - m) ^ 6 := by positivity
  have hab_err : |Real.log (gb / t) * Real.log ((t + 2) / 3) - pa * pb| ≤
      2 * ((Ahi - Alo) + (Bhi - Blo)) + 2 / 3 * b1 ^ 6 * (t - m) ^ 6 := by
    have hid : Real.log (gb / t) * Real.log ((t + 2) / 3) - pa * pb =
        (Real.log (gb / t) - pa) * Real.log ((t + 2) / 3) + pa * (Real.log ((t + 2) / 3) - pb) := by ring
    rw [hid]
    have ht1 := abs_add_le ((Real.log (gb / t) - pa) * Real.log ((t + 2) / 3))
      (pa * (Real.log ((t + 2) / 3) - pb))
    rw [abs_mul, abs_mul] at ht1
    have hm1 : |Real.log (gb / t) - pa| * |Real.log ((t + 2) / 3)| ≤
        ((Ahi - Alo) + 5 / 27 * b1 ^ 6 * (t - m) ^ 6) * (5 / 4) :=
      mul_le_mul ha_err hb_abs (abs_nonneg _) (by positivity)
    have hm2 : |pa| * |Real.log ((t + 2) / 3) - pb| ≤ 2 * ((Bhi - Blo) + 5 / 27 * b1 ^ 6 * (t - m) ^ 6) :=
      mul_le_mul hpa_abs hb_err (abs_nonneg _) (by norm_num)
    linarith only [ht1, hm1, hm2, hepsA, hepsB, hb6x6_pos]
  have htele_err : |(1 + d * (t - m)) * (c0 + c1 * (t - m) + c2 * (t - m) ^ 2 +
      c3 * (t - m) ^ 3 + c4 * (t - m) ^ 4 + c5 * (t - m) ^ 5) - pa * pb| ≤
      E6 * (t - m) ^ 6 :=
    quad_prod5_tele_err (t - m) h b1 b2 d c0 c1 c2 c3 c4 c5 e6 e7 e8 e9 e10 E6 Alo Blo
      htm hc0 hc1 hc2 hc3 hc4 hc5 he6 he7 he8 he9 he10 hE6
  have h_inner : ((c0 - 3 * ((Ahi - Alo) + (Bhi - Blo))) + c1 * (t - m) + c2 * (t - m) ^ 2 +
      c3 * (t - m) ^ 3 + c4 * (t - m) ^ 4 + c5 * (t - m) ^ 5 +
      (-(2 * E6 + b1 ^ 6)) * (t - m) ^ 6) ≤
      Real.log (gb / t) * Real.log ((t + 2) / 3) / (1 + d * (t - m)) := by
    rw [le_div_iff₀ hd_pos]
    obtain ⟨a1, a2⟩ := abs_le.mp hab_err
    obtain ⟨t1, t2⟩ := abs_le.mp htele_err
    have hdiff : (1 + d * (t - m)) * (c0 + c1 * (t - m) + c2 * (t - m) ^ 2 +
        c3 * (t - m) ^ 3 + c4 * (t - m) ^ 4 + c5 * (t - m) ^ 5) -
        Real.log (gb / t) * Real.log ((t + 2) / 3) ≤
        2 * ((Ahi - Alo) + (Bhi - Blo)) + (E6 + 2 / 3 * b1 ^ 6) * (t - m) ^ 6 := by
      linarith only [a1, a2, t1, t2]
    have hEx6_nn : 0 ≤ E6 * (t - m) ^ 6 := mul_nonneg hE6_nn hx6_pos
    have hscale : 2 * ((Ahi - Alo) + (Bhi - Blo)) + (E6 + 2 / 3 * b1 ^ 6) * (t - m) ^ 6 ≤
        (3 * ((Ahi - Alo) + (Bhi - Blo)) + (2 * E6 + b1 ^ 6) * (t - m) ^ 6) * (1 + d * (t - m)) := by
      have h_rhs0 : 0 ≤ 3 * ((Ahi - Alo) + (Bhi - Blo)) + (2 * E6 + b1 ^ 6) * (t - m) ^ 6 := by
        linarith only [hepsA, hepsB, hEx6_nn, hb6x6_pos]
      have hm9 := mul_le_mul_of_nonneg_left hd1 h_rhs0
      linarith only [hm9, hepsA, hepsB, hEx6_nn, hb6x6_pos]
    have h_alg : ((c0 - 3 * ((Ahi - Alo) + (Bhi - Blo))) + c1 * (t - m) + c2 * (t - m) ^ 2 +
        c3 * (t - m) ^ 3 + c4 * (t - m) ^ 4 + c5 * (t - m) ^ 5 +
        (-(2 * E6 + b1 ^ 6)) * (t - m) ^ 6) * (1 + d * (t - m)) =
        (1 + d * (t - m)) * (c0 + c1 * (t - m) + c2 * (t - m) ^ 2 +
          c3 * (t - m) ^ 3 + c4 * (t - m) ^ 4 + c5 * (t - m) ^ 5) -
          (3 * ((Ahi - Alo) + (Bhi - Blo)) + (2 * E6 + b1 ^ 6) * (t - m) ^ 6) * (1 + d * (t - m)) := by ring
    linarith only [hdiff, hscale, h_alg]
  rw [ht1_id, ← div_div]
  exact div_le_div_of_nonneg_right h_inner hm1_pos.le

private lemma quad_prod5_sub (gb M_gb M_m2 u v m h b1 b2 d c0 c1 c2 c3 c4 c5 e6 e7 e8 e9 e10 E6 Alo Ahi Blo Bhi out_lo : ℝ)
    (hA : Alo ≤ Real.log M_gb ∧ Real.log M_gb ≤ Ahi)
    (hB : Blo ≤ Real.log M_m2 ∧ Real.log M_m2 ≤ Bhi)
    (h_arith : u ≤ v ∧ m = (u + v) / 2 ∧ h = (v - u) / 2 ∧
      M_gb = gb / m ∧ M_m2 = (m + 2) / 3 ∧
      1 ≤ m ∧ b1 * h ≤ 1 / 10 ∧ 0 < gb ∧ 0 ≤ E6 ∧
      m * b1 = 1 ∧ (m + 2) * b2 = 1 ∧ (m + 1) * d = 1 ∧
      c0 = Alo * Blo ∧
      c1 = Alo * b2 - Blo * b1 - d * c0 ∧
      c2 = -Alo * b2 ^ 2 / 2 + Blo * b1 ^ 2 / 2 - b1 * b2 - d * c1 ∧
      c3 = Alo * b2 ^ 3 / 3 - Blo * b1 ^ 3 / 3 + b1 * b2 ^ 2 / 2 + b1 ^ 2 * b2 / 2 - d * c2 ∧
      c4 = -Alo * b2 ^ 4 / 4 + Blo * b1 ^ 4 / 4 - b1 * b2 ^ 3 / 3 - b1 ^ 2 * b2 ^ 2 / 4 - b1 ^ 3 * b2 / 3 - d * c3 ∧
      c5 = Alo * b2 ^ 5 / 5 - Blo * b1 ^ 5 / 5 + b1 * b2 ^ 4 / 4 + b1 ^ 2 * b2 ^ 3 / 6 + b1 ^ 3 * b2 ^ 2 / 6 + b1 ^ 4 * b2 / 4 - d * c4 ∧
      e6 = d * c5 + b1 * b2 ^ 5 / 5 + b1 ^ 2 * b2 ^ 4 / 8 + b1 ^ 3 * b2 ^ 3 / 9 + b1 ^ 4 * b2 ^ 2 / 8 + b1 ^ 5 * b2 / 5 ∧
      e7 = -b1 ^ 2 * b2 ^ 5 / 10 - b1 ^ 3 * b2 ^ 4 / 12 - b1 ^ 4 * b2 ^ 3 / 12 - b1 ^ 5 * b2 ^ 2 / 10 ∧
      e8 = b1 ^ 3 * b2 ^ 5 / 15 + b1 ^ 4 * b2 ^ 4 / 16 + b1 ^ 5 * b2 ^ 3 / 15 ∧
      e9 = -b1 ^ 4 * b2 ^ 5 / 20 - b1 ^ 5 * b2 ^ 4 / 20 ∧
      e10 = b1 ^ 5 * b2 ^ 5 / 25 ∧
      |e6| + |e7| * h + |e8| * h ^ 2 + |e9| * h ^ 3 + |e10| * h ^ 4 ≤ E6 ∧
      (-1 / 10 ≤ Alo ∧ Alo ≤ 3 / 2 ∧ Ahi - Alo ≤ 1 / 100) ∧
      (0 ≤ Blo ∧ Blo ≤ 1 ∧ Bhi - Blo ≤ 1 / 100) ∧
      out_lo ≤ quadProd5Lo m h b1 c0 c2 c4 E6 Alo Ahi Blo Bhi) :
    IntervalIntegrable (fun t => Real.log (gb / t) * Real.log ((t + 2) / 3) / (t + 1)) volume u v ∧
      out_lo ≤ ∫ t in u..v, Real.log (gb / t) * Real.log ((t + 2) / 3) / (t + 1) := by
  rcases h_arith with ⟨huv, hm, hh, hM_gb, hM_m2, hm1, hhm, hgb, hE6_nn,
    hb1_eq, hb2_eq, hd_eq, hc0, hc1, hc2, hc3, hc4, hc5, he6, he7, he8, he9, he10,
    hE6, hA_range, hB_range, hout_lo⟩
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
        c3 * (t - m) ^ 3 + c4 * (t - m) ^ 4 + c5 * (t - m) ^ 5 +
        (-(2 * E6 + b1 ^ 6)) * (t - m) ^ 6) / (m + 1)) volume u v :=
    ((continuous_centered_poly6 (c0 - 3 * ((Ahi - Alo) + (Bhi - Blo))) c1 c2 c3 c4 c5 (-(2 * E6 + b1 ^ 6)) m).div_const (m + 1)).intervalIntegrable u v
  have hmono : ∫ t in u..v, (((c0 - 3 * ((Ahi - Alo) + (Bhi - Blo))) + c1 * (t - m) + c2 * (t - m) ^ 2 +
      c3 * (t - m) ^ 3 + c4 * (t - m) ^ 4 + c5 * (t - m) ^ 5 +
      (-(2 * E6 + b1 ^ 6)) * (t - m) ^ 6) / (m + 1)) ≤
      ∫ t in u..v, Real.log (gb / t) * Real.log ((t + 2) / 3) / (t + 1) := by
    apply integral_mono_on huv hpoly_int hf_int
    intro t ht
    obtain ⟨htm, hx1, hx2, _, hd1, hb1_1, hb2_1⟩ := h_pt t ht
    exact quad_prod5_pt_lb gb m h t b1 b2 d c0 c1 c2 c3 c4 c5 e6 e7 e8 e9 e10 E6 Alo Ahi Blo Bhi
      hm1 hgb hE6_nn hb1_pos hb2_pos hb2_le1 (ht_id t) (ht2_id t) (ht1_id t)
      htm hx1 hx2 hd1 hb1_1 hb2_1 hc0 hc1 hc2 hc3 hc4 hc5 he6 he7 he8 he9 he10 hE6
      hA_range hB_range hA hB
  rw [intervalIntegral.integral_div] at hmono
  have hev := integral_centered_poly6 (c0 - 3 * ((Ahi - Alo) + (Bhi - Blo))) c1 c2 c3 c4 c5 (-(2 * E6 + b1 ^ 6)) u v m h hm hh
  rw [hev] at hmono
  dsimp only [quadProd5Lo] at hout_lo
  refine le_trans hout_lo (le_trans ?_ hmono)
  apply div_le_div_of_nonneg_right _ hm1_pos.le
  linarith only []

private lemma chain_int_bounds {f : ℝ → ℝ} {u m v lo1 hi1 lo2 hi2 lo hi : ℝ}
    (h1 : IntervalIntegrable f volume u m ∧ lo1 ≤ ∫ t in u..m, f t ∧ ∫ t in u..m, f t ≤ hi1)
    (h2 : IntervalIntegrable f volume m v ∧ lo2 ≤ ∫ t in m..v, f t ∧ ∫ t in m..v, f t ≤ hi2)
    (h_arith : lo ≤ lo1 + lo2 ∧ hi1 + hi2 ≤ hi) :
    IntervalIntegrable f volume u v ∧ lo ≤ ∫ t in u..v, f t ∧ ∫ t in u..v, f t ≤ hi := by
  refine ⟨h1.1.trans h2.1, ?_, ?_⟩
  · rw [← integral_add_adjacent_intervals h1.1 h2.1]; linarith [h1.2.1, h2.2.1, h_arith.1]
  · rw [← integral_add_adjacent_intervals h1.1 h2.1]; linarith [h1.2.2, h2.2.2, h_arith.2]

private lemma chain4_int_bounds {f : ℝ → ℝ} {p0 p1 p2 p3 p4 l1 h1 l2 h2 l3 h3 l4 h4 lo hi : ℝ}
    (i1 : IntervalIntegrable f volume p0 p1 ∧ l1 ≤ ∫ t in p0..p1, f t ∧ ∫ t in p0..p1, f t ≤ h1)
    (i2 : IntervalIntegrable f volume p1 p2 ∧ l2 ≤ ∫ t in p1..p2, f t ∧ ∫ t in p1..p2, f t ≤ h2)
    (i3 : IntervalIntegrable f volume p2 p3 ∧ l3 ≤ ∫ t in p2..p3, f t ∧ ∫ t in p2..p3, f t ≤ h3)
    (i4 : IntervalIntegrable f volume p3 p4 ∧ l4 ≤ ∫ t in p3..p4, f t ∧ ∫ t in p3..p4, f t ≤ h4)
    (h_arith : lo ≤ l1 + l2 + l3 + l4 ∧ h1 + h2 + h3 + h4 ≤ hi) :
    IntervalIntegrable f volume p0 p4 ∧ lo ≤ ∫ t in p0..p4, f t ∧ ∫ t in p0..p4, f t ≤ hi := by
  have i12 := i1.1.trans i2.1
  have i123 := i12.trans i3.1
  refine ⟨i123.trans i4.1, ?_, ?_⟩
  · rw [← integral_add_adjacent_intervals i123 i4.1, ← integral_add_adjacent_intervals i12 i3.1,
      ← integral_add_adjacent_intervals i1.1 i2.1]
    linarith [i1.2.1, i2.2.1, i3.2.1, i4.2.1, h_arith.1]
  · rw [← integral_add_adjacent_intervals i123 i4.1, ← integral_add_adjacent_intervals i12 i3.1,
      ← integral_add_adjacent_intervals i1.1 i2.1]
    linarith [i1.2.2, i2.2.2, i3.2.2, i4.2.2, h_arith.2]

private lemma chain_int_lb {f : ℝ → ℝ} {u m v lo1 lo2 lo : ℝ}
    (h1 : IntervalIntegrable f volume u m ∧ lo1 ≤ ∫ t in u..m, f t)
    (h2 : IntervalIntegrable f volume m v ∧ lo2 ≤ ∫ t in m..v, f t)
    (hlo : lo ≤ lo1 + lo2) :
    IntervalIntegrable f volume u v ∧ lo ≤ ∫ t in u..v, f t := by
  refine ⟨h1.1.trans h2.1, ?_⟩
  rw [← integral_add_adjacent_intervals h1.1 h2.1]; linarith [h1.2, h2.2]

private lemma chain4_int_lb {f : ℝ → ℝ} {p0 p1 p2 p3 p4 l1 l2 l3 l4 lo : ℝ}
    (i1 : IntervalIntegrable f volume p0 p1 ∧ l1 ≤ ∫ t in p0..p1, f t)
    (i2 : IntervalIntegrable f volume p1 p2 ∧ l2 ≤ ∫ t in p1..p2, f t)
    (i3 : IntervalIntegrable f volume p2 p3 ∧ l3 ≤ ∫ t in p2..p3, f t)
    (i4 : IntervalIntegrable f volume p3 p4 ∧ l4 ≤ ∫ t in p3..p4, f t)
    (hlo : lo ≤ l1 + l2 + l3 + l4) :
    IntervalIntegrable f volume p0 p4 ∧ lo ≤ ∫ t in p0..p4, f t := by
  have i12 := i1.1.trans i2.1
  have i123 := i12.trans i3.1
  refine ⟨i123.trans i4.1, ?_⟩
  rw [← integral_add_adjacent_intervals i123 i4.1, ← integral_add_adjacent_intervals i12 i3.1,
    ← integral_add_adjacent_intervals i1.1 i2.1]
  linarith [i1.2, i2.2, i3.2, i4.2]

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


private lemma add3_int_lb {f0 f1 f2 : ℝ → ℝ} {a b l0 l1 l2 l : ℝ}
    (h0 : IntervalIntegrable f0 volume a b ∧ l0 ≤ ∫ t in a..b, f0 t)
    (h1 : IntervalIntegrable f1 volume a b ∧ l1 ≤ ∫ t in a..b, f1 t)
    (h2 : IntervalIntegrable f2 volume a b ∧ l2 ≤ ∫ t in a..b, f2 t)
    (hl : l ≤ l0 + l1 + l2) :
    IntervalIntegrable (fun t => ((f0 t) + (f1 t)) + (f2 t)) volume a b ∧
      l ≤ ∫ t in a..b, (((f0 t) + (f1 t)) + (f2 t)) := by
  have s1 := h0.1.add h1.1
  refine ⟨s1.add h2.1, ?_⟩
  rw [integral_add s1 h2.1, integral_add h0.1 h1.1]
  linarith [h0.2, h1.2, h2.2]

private lemma add10_int_lb {f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 : ℝ → ℝ}
    {a b l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l : ℝ}
    (h0 : IntervalIntegrable f0 volume a b ∧ l0 ≤ ∫ t in a..b, f0 t)
    (h1 : IntervalIntegrable f1 volume a b ∧ l1 ≤ ∫ t in a..b, f1 t)
    (h2 : IntervalIntegrable f2 volume a b ∧ l2 ≤ ∫ t in a..b, f2 t)
    (h3 : IntervalIntegrable f3 volume a b ∧ l3 ≤ ∫ t in a..b, f3 t)
    (h4 : IntervalIntegrable f4 volume a b ∧ l4 ≤ ∫ t in a..b, f4 t)
    (h5 : IntervalIntegrable f5 volume a b ∧ l5 ≤ ∫ t in a..b, f5 t)
    (h6 : IntervalIntegrable f6 volume a b ∧ l6 ≤ ∫ t in a..b, f6 t)
    (h7 : IntervalIntegrable f7 volume a b ∧ l7 ≤ ∫ t in a..b, f7 t)
    (h8 : IntervalIntegrable f8 volume a b ∧ l8 ≤ ∫ t in a..b, f8 t)
    (h9 : IntervalIntegrable f9 volume a b ∧ l9 ≤ ∫ t in a..b, f9 t)
    (hl : l ≤ l0 + l1 + l2 + l3 + l4 + l5 + l6 + l7 + l8 + l9) :
    IntervalIntegrable (fun t => (((((((((f0 t) + (f1 t)) + (f2 t)) + (f3 t)) + (f4 t)) + (f5 t)) + (f6 t)) + (f7 t)) + (f8 t)) + (f9 t)) volume a b ∧
      l ≤ ∫ t in a..b, ((((((((((f0 t) + (f1 t)) + (f2 t)) + (f3 t)) + (f4 t)) + (f5 t)) + (f6 t)) + (f7 t)) + (f8 t)) + (f9 t)) := by
  have s1 := h0.1.add h1.1
  have s2 := s1.add h2.1
  have s3 := s2.add h3.1
  have s4 := s3.add h4.1
  have s5 := s4.add h5.1
  have s6 := s5.add h6.1
  have s7 := s6.add h7.1
  have s8 := s7.add h8.1
  refine ⟨s8.add h9.1, ?_⟩
  rw [integral_add s8 h9.1, integral_add s7 h8.1, integral_add s6 h7.1, integral_add s5 h6.1,
    integral_add s4 h5.1, integral_add s3 h4.1, integral_add s2 h3.1, integral_add s1 h2.1,
    integral_add h0.1 h1.1]
  linarith [h0.2, h1.2, h2.2, h3.2, h4.2, h5.2, h6.2, h7.2, h8.2, h9.2]

private lemma hlog_1 : (232031864069 / 5000000000000 : ℝ) ≤ Real.log (419 / 400 : ℝ) ∧ Real.log (419 / 400 : ℝ) ≤ (92812745629 / 2000000000000 : ℝ) :=
  log_rat_bounds (419 / 400 : ℝ) (7 / 2507 : ℝ) (-3) (-1) (2) (232031864069 / 5000000000000 : ℝ) (92812745629 / 2000000000000 : ℝ)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hqsub_2 :
    IntervalIntegrable (fun t => Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t)) volume (1 : ℝ) (257 / 200 : ℝ) ∧
      (15005794871 / 2500000000000 : ℝ) ≤ ∫ t in (1 : ℝ)..(257 / 200 : ℝ), Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (1 : ℝ)..(257 / 200 : ℝ), Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t) ≤ (60023295491 / 10000000000000 : ℝ) :=
  quad_log_div_sub (2 / 3 : ℝ) (1 / 3 : ℝ) (1 : ℝ) (1 : ℝ) (1 : ℝ) (257 / 200 : ℝ) (457 / 400 : ℝ) (57 / 400 : ℝ)
    (419 / 400 : ℝ) (857 / 400 : ℝ) (400 / 1257 : ℝ) (400 / 857 : ℝ) (400 / 857 : ℝ) (232031864069 / 5000000000000 : ℝ) (92812745629 / 2000000000000 : ℝ) (15005794871 / 2500000000000 : ℝ) (60023295491 / 10000000000000 : ℝ)
    hlog_1 (by norm_num [quadLogLo, quadLogHi])

private lemma hlog_3 : (66609421893 / 500000000000 : ℝ) ≤ Real.log (457 / 400 : ℝ) ∧ Real.log (457 / 400 : ℝ) ≤ (266437687573 / 2000000000000 : ℝ) :=
  log_rat_bounds (457 / 400 : ℝ) (7 / 907 : ℝ) (-3) (2) (0) (66609421893 / 500000000000 : ℝ) (266437687573 / 2000000000000 : ℝ)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hqsub_4 :
    IntervalIntegrable (fun t => Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t)) volume (257 / 200 : ℝ) (157 / 100 : ℝ) ∧
      (77644355381 / 5000000000000 : ℝ) ≤ ∫ t in (257 / 200 : ℝ)..(157 / 100 : ℝ), Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (257 / 200 : ℝ)..(157 / 100 : ℝ), Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t) ≤ (155288759821 / 10000000000000 : ℝ) :=
  quad_log_div_sub (2 / 3 : ℝ) (1 / 3 : ℝ) (1 : ℝ) (1 : ℝ) (257 / 200 : ℝ) (157 / 100 : ℝ) (571 / 400 : ℝ) (57 / 400 : ℝ)
    (457 / 400 : ℝ) (971 / 400 : ℝ) (400 / 1371 : ℝ) (400 / 971 : ℝ) (400 / 971 : ℝ) (66609421893 / 500000000000 : ℝ) (266437687573 / 2000000000000 : ℝ) (77644355381 / 5000000000000 : ℝ) (155288759821 / 10000000000000 : ℝ)
    hlog_3 (by norm_num [quadLogLo, quadLogHi])

private lemma hlog_5 : (111571775657 / 500000000000 : ℝ) ≤ Real.log (5 / 4 : ℝ) ∧ Real.log (5 / 4 : ℝ) ≤ (278929439143 / 1250000000000 : ℝ) :=
  log_rat_bounds (5 / 4 : ℝ) (0 : ℝ) (-2) (0) (1) (111571775657 / 500000000000 : ℝ) (278929439143 / 1250000000000 : ℝ)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hqsub_6 :
    IntervalIntegrable (fun t => Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t)) volume (157 / 100 : ℝ) (193 / 100 : ℝ) ∧
      (145326961541 / 5000000000000 : ℝ) ≤ ∫ t in (157 / 100 : ℝ)..(193 / 100 : ℝ), Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (157 / 100 : ℝ)..(193 / 100 : ℝ), Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t) ≤ (11626161187 / 400000000000 : ℝ) :=
  quad_log_div_sub (2 / 3 : ℝ) (1 / 3 : ℝ) (1 : ℝ) (1 : ℝ) (157 / 100 : ℝ) (193 / 100 : ℝ) (7 / 4 : ℝ) (9 / 50 : ℝ)
    (5 / 4 : ℝ) (11 / 4 : ℝ) (4 / 15 : ℝ) (4 / 11 : ℝ) (4 / 11 : ℝ) (111571775657 / 500000000000 : ℝ) (278929439143 / 1250000000000 : ℝ) (145326961541 / 5000000000000 : ℝ) (11626161187 / 400000000000 : ℝ)
    hlog_5 (by norm_num [quadLogLo, quadLogHi])

private lemma hlog_7 : (196376426413 / 625000000000 : ℝ) ≤ Real.log (1643 / 1200 : ℝ) ∧ Real.log (1643 / 1200 : ℝ) ≤ (628404564523 / 2000000000000 : ℝ) :=
  log_rat_bounds (1643 / 1200 : ℝ) (23 / 3263 : ℝ) (-2) (3) (-1) (196376426413 / 625000000000 : ℝ) (628404564523 / 2000000000000 : ℝ)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hqsub_8 :
    IntervalIntegrable (fun t => Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t)) volume (193 / 100 : ℝ) (457 / 200 : ℝ) ∧
      (44754550681 / 1250000000000 : ℝ) ≤ ∫ t in (193 / 100 : ℝ)..(457 / 200 : ℝ), Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (193 / 100 : ℝ)..(457 / 200 : ℝ), Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t) ≤ (179018223553 / 5000000000000 : ℝ) :=
  quad_log_div_sub (2 / 3 : ℝ) (1 / 3 : ℝ) (1 : ℝ) (1 : ℝ) (193 / 100 : ℝ) (457 / 200 : ℝ) (843 / 400 : ℝ) (71 / 400 : ℝ)
    (1643 / 1200 : ℝ) (1243 / 400 : ℝ) (400 / 1643 : ℝ) (400 / 1243 : ℝ) (400 / 1243 : ℝ) (196376426413 / 625000000000 : ℝ) (628404564523 / 2000000000000 : ℝ) (44754550681 / 1250000000000 : ℝ) (179018223553 / 5000000000000 : ℝ)
    hlog_7 (by norm_num [quadLogLo, quadLogHi])

private lemma hlog_9 : (3970968584373 / 10000000000000 : ℝ) ≤ Real.log (119 / 80 : ℝ) ∧ Real.log (119 / 80 : ℝ) ≤ (198548429219 / 500000000000 : ℝ) :=
  log_rat_bounds (119 / 80 : ℝ) (13 / 6413 : ℝ) (3) (-3) (1) (3970968584373 / 10000000000000 : ℝ) (198548429219 / 500000000000 : ℝ)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hqsub_10 :
    IntervalIntegrable (fun t => Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t)) volume (457 / 200 : ℝ) (66 / 25 : ℝ) ∧
      (406519905429 / 10000000000000 : ℝ) ≤ ∫ t in (457 / 200 : ℝ)..(66 / 25 : ℝ), Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (457 / 200 : ℝ)..(66 / 25 : ℝ), Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t) ≤ (406519925211 / 10000000000000 : ℝ) :=
  quad_log_div_sub (2 / 3 : ℝ) (1 / 3 : ℝ) (1 : ℝ) (1 : ℝ) (457 / 200 : ℝ) (66 / 25 : ℝ) (197 / 80 : ℝ) (71 / 400 : ℝ)
    (119 / 80 : ℝ) (277 / 80 : ℝ) (80 / 357 : ℝ) (80 / 277 : ℝ) (80 / 277 : ℝ) (3970968584373 / 10000000000000 : ℝ) (198548429219 / 500000000000 : ℝ) (406519905429 / 10000000000000 : ℝ) (406519925211 / 10000000000000 : ℝ)
    hlog_9 (by norm_num [quadLogLo, quadLogHi])

private lemma hlog_11 : (2370808196971 / 5000000000000 : ℝ) ≤ Real.log (241 / 150 : ℝ) ∧ Real.log (241 / 150 : ℝ) ≤ (2370808196973 / 5000000000000 : ℝ) :=
  log_rat_bounds (241 / 150 : ℝ) (1 / 481 : ℝ) (3) (0) (-1) (2370808196971 / 5000000000000 : ℝ) (2370808196973 / 5000000000000 : ℝ)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hqsub_12 :
    IntervalIntegrable (fun t => Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t)) volume (66 / 25 : ℝ) (3 : ℝ) ∧
      (44641195601 / 1000000000000 : ℝ) ≤ ∫ t in (66 / 25 : ℝ)..(3 : ℝ), Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (66 / 25 : ℝ)..(3 : ℝ), Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t) ≤ (446411967103 / 10000000000000 : ℝ) :=
  quad_log_div_sub (2 / 3 : ℝ) (1 / 3 : ℝ) (1 : ℝ) (1 : ℝ) (66 / 25 : ℝ) (3 : ℝ) (141 / 50 : ℝ) (9 / 50 : ℝ)
    (241 / 150 : ℝ) (191 / 50 : ℝ) (50 / 241 : ℝ) (50 / 191 : ℝ) (50 / 191 : ℝ) (2370808196971 / 5000000000000 : ℝ) (2370808196973 / 5000000000000 : ℝ) (44641195601 / 1000000000000 : ℝ) (446411967103 / 10000000000000 : ℝ)
    hlog_11 (by norm_num [quadLogLo, quadLogHi])

private lemma hqchain_13 :
    IntervalIntegrable (fun t => Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t)) volume (1 : ℝ) (457 / 200 : ℝ) ∧
      (108000277347 / 1250000000000 : ℝ) ≤ ∫ t in (1 : ℝ)..(457 / 200 : ℝ), Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (1 : ℝ)..(457 / 200 : ℝ), Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t) ≤ (864002532093 / 10000000000000 : ℝ) :=
  chain4_int_bounds hqsub_2 hqsub_4 hqsub_6 hqsub_8 (by norm_num)

private lemma hqchain_14 :
    IntervalIntegrable (fun t => Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t)) volume (1 : ℝ) (66 / 25 : ℝ) ∧
      (254104424841 / 2000000000000 : ℝ) ≤ ∫ t in (1 : ℝ)..(66 / 25 : ℝ), Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (1 : ℝ)..(66 / 25 : ℝ), Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t) ≤ (158815307163 / 1250000000000 : ℝ) :=
  chain_int_bounds hqchain_13 hqsub_10 (by norm_num)

private lemma hqchain_15 :
    IntervalIntegrable (fun t => Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t)) volume (1 : ℝ) (3 : ℝ) ∧
      (343386816043 / 2000000000000 : ℝ) ≤ ∫ t in (1 : ℝ)..(3 : ℝ), Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (1 : ℝ)..(3 : ℝ), Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t) ≤ (1716934424407 / 10000000000000 : ℝ) :=
  chain_int_bounds hqchain_14 hqsub_12 (by norm_num)

private lemma hfga_16 : (0 : ℝ) ≤ ∫ s in (1 : ℝ)..(1 : ℝ), Real.log ((s + 2) / 3) / (s + 1) := by
  rw [integral_same]

private lemma hlog_17 : (7884573603639 / 10000000000000 : ℝ) ≤ Real.log (11 / 5 : ℝ) ∧ Real.log (11 / 5 : ℝ) ≤ (3942286801823 / 5000000000000 : ℝ) :=
  log_rat_bounds (11 / 5 : ℝ) (1 / 109 : ℝ) (1) (3) (-2) (7884573603639 / 10000000000000 : ℝ) (3942286801823 / 5000000000000 : ℝ)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hlog_18 : (3580683493921 / 5000000000000 : ℝ) ≤ Real.log (88 / 43 : ℝ) ∧ Real.log (88 / 43 : ℝ) ≤ (143227339757 / 200000000000 : ℝ) :=
  log_rat_bounds (88 / 43 : ℝ) (37 / 7003 : ℝ) (-3) (4) (-1) (3580683493921 / 5000000000000 : ℝ) (143227339757 / 200000000000 : ℝ)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hlog_19 : (246926125899 / 10000000000000 : ℝ) ≤ Real.log (41 / 40 : ℝ) ∧ Real.log (41 / 40 : ℝ) ≤ (61731531477 / 2500000000000 : ℝ) :=
  log_rat_bounds (41 / 40 : ℝ) (1 / 2049 : ℝ) (7) (0) (-3) (246926125899 / 10000000000000 : ℝ) (61731531477 / 2500000000000 : ℝ)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hpsub_20 :
    IntervalIntegrable (fun t => Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1)) volume (1 : ℝ) (23 / 20 : ℝ) ∧
      (610161307 / 500000000000 : ℝ) ≤ ∫ t in (1 : ℝ)..(23 / 20 : ℝ), Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1) :=
  quad_prod5_sub (11 / 5 : ℝ) (88 / 43 : ℝ) (41 / 40 : ℝ) (1 : ℝ) (23 / 20 : ℝ) (43 / 40 : ℝ) (3 / 40 : ℝ)
    (40 / 43 : ℝ) (40 / 123 : ℝ) (40 / 83 : ℝ) (884164303224408047159979 / 50000000000000000000000000 : ℝ) (1331492828937013745043022543 / 6611250000000000000000000000 : ℝ) (-30964032179120097250032546229927 / 72556320093750000000000000000000 : ℝ) (948718404865447286200411411030251709 / 2388846096674627343750000000000000000 : ℝ) (-100198997441950752983207003477641991221 / 323664315259538467207031250000000000000 : ℝ) (21953338720861548595754625240446709272332463 / 95906988064916333845073793457031250000000000 : ℝ)
    (33926808588226229043254625240446709272332463 / 199007000234701392728528121423339843750000000 : ℝ) (-4864262144000000 / 459859672464436161 : ℝ) (28752527360000000 / 12416211156539776347 : ℝ) (-2175795200000000 / 4138737052179925449 : ℝ) (419430400000000 / 4138737052179925449 : ℝ) (8564353 / 50000000 : ℝ)
    (3580683493921 / 5000000000000 : ℝ) (143227339757 / 200000000000 : ℝ) (246926125899 / 10000000000000 : ℝ) (61731531477 / 2500000000000 : ℝ) (610161307 / 500000000000 : ℝ)
    hlog_18 hlog_19 (by norm_num [quadProd5Lo])

private lemma hlog_21 : (5855165163673 / 10000000000000 : ℝ) ≤ Real.log (88 / 49 : ℝ) ∧ Real.log (88 / 49 : ℝ) ≤ (2927582581839 / 5000000000000 : ℝ) :=
  log_rat_bounds (88 / 49 : ℝ) (1 / 197 : ℝ) (4) (-2) (0) (5855165163673 / 10000000000000 : ℝ) (2927582581839 / 5000000000000 : ℝ)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hlog_22 : (723206615793 / 10000000000000 : ℝ) ≤ Real.log (43 / 40 : ℝ) ∧ Real.log (43 / 40 : ℝ) ≤ (723206615799 / 10000000000000 : ℝ) :=
  log_rat_bounds (43 / 40 : ℝ) (1 / 257 : ℝ) (4) (-1) (-1) (723206615793 / 10000000000000 : ℝ) (723206615799 / 10000000000000 : ℝ)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hpsub_23 :
    IntervalIntegrable (fun t => Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1)) volume (23 / 20 : ℝ) (13 / 10 : ℝ) ∧
      (7040608643 / 2500000000000 : ℝ) ≤ ∫ t in (23 / 20 : ℝ)..(13 / 10 : ℝ), Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1) :=
  quad_prod5_sub (11 / 5 : ℝ) (88 / 49 : ℝ) (43 / 40 : ℝ) (23 / 20 : ℝ) (13 / 10 : ℝ) (49 / 40 : ℝ) (3 / 40 : ℝ)
    (40 / 49 : ℝ) (40 / 129 : ℝ) (40 / 89 : ℝ) (4234494182929017271687689 / 100000000000000000000000000 : ℝ) (145546163498290881825662117831 / 1406422500000000000000000000000 : ℝ) (-6006996978800894877820010246809751 / 19780242485062500000000000000000000 : ℝ) (226800363255774010457426854310253308213 / 834581342593434417187500000000000000000 : ℝ) (-766151955296358870504177282131703720404791 / 3912579927678715055356289062500000000000000 : ℝ) (7232784221048061855694381783468659216678683911 / 55027404433357176249418304540039062500000000000 : ℝ)
    (11010962508975917342659381783468659216678683911 / 122435974864219717154955727601586914062500000000 : ℝ) (-52460797952000000 / 10090877909591135601 : ℝ) (32725975040000000 / 30272633728773406803 : ℝ) (-2333081600000000 / 10090877909591135601 : ℝ) (419430400000000 / 10090877909591135601 : ℝ) (9032851 / 100000000 : ℝ)
    (5855165163673 / 10000000000000 : ℝ) (2927582581839 / 5000000000000 : ℝ) (723206615793 / 10000000000000 : ℝ) (723206615799 / 10000000000000 : ℝ) (7040608643 / 2500000000000 : ℝ)
    hlog_21 hlog_22 (by norm_num [quadProd5Lo])

private lemma hlog_24 : (1147884033053 / 2500000000000 : ℝ) ≤ Real.log (220 / 139 : ℝ) ∧ Real.log (220 / 139 : ℝ) ≤ (4591536132221 / 10000000000000 : ℝ) :=
  log_rat_bounds (220 / 139 : ℝ) (7 / 8903 : ℝ) (7) (-4) (0) (1147884033053 / 2500000000000 : ℝ) (4591536132221 / 10000000000000 : ℝ)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hlog_25 : (30554408181 / 250000000000 : ℝ) ≤ Real.log (113 / 100 : ℝ) ∧ Real.log (113 / 100 : ℝ) ≤ (244435265449 / 2000000000000 : ℝ) :=
  log_rat_bounds (113 / 100 : ℝ) (1 / 451 : ℝ) (-3) (2) (0) (30554408181 / 250000000000 : ℝ) (244435265449 / 2000000000000 : ℝ)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hpsub_26 :
    IntervalIntegrable (fun t => Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1)) volume (13 / 10 : ℝ) (37 / 25 : ℝ) ∧
      (41834059061 / 10000000000000 : ℝ) ≤ ∫ t in (13 / 10 : ℝ)..(37 / 25 : ℝ), Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1) :=
  quad_prod5_sub (11 / 5 : ℝ) (220 / 139 : ℝ) (113 / 100 : ℝ) (13 / 10 : ℝ) (37 / 25 : ℝ) (139 / 100 : ℝ) (9 / 100 : ℝ)
    (100 / 139 : ℝ) (100 / 339 : ℝ) (100 / 239 : ℝ) (35072917290353857606593 / 625000000000000000000000 : ℝ) (1691921166792661625719731247 / 70386993750000000000000000000 : ℝ) (-1669615479905214346135914456089887 / 7926926222660062500000000000000000 : ℝ) (494192332253176377488696831006234695981 / 2678172031157207652298125000000000000000 : ℝ) (-461429711550290115124512993023430217399021 / 3723624257155302326711314518750000000000000 : ℝ) (861357597275914703529575067388714269549600250607 / 11322491788039910010462277333295349937500000000000 : ℝ)
    (1298574395072774713041156098638714269549600250607 / 27060755373415384925004842826575886350625000000000 : ℝ) (-201379010000000000000 / 77437484638204254819867 : ℝ) (356835875000000000000 / 696937361743838293378803 : ℝ) (-23900000000000000000 / 232312453914612764459601 : ℝ) (4000000000000000000 / 232312453914612764459601 : ℝ) (1205641 / 25000000 : ℝ)
    (1147884033053 / 2500000000000 : ℝ) (4591536132221 / 10000000000000 : ℝ) (30554408181 / 250000000000 : ℝ) (244435265449 / 2000000000000 : ℝ) (41834059061 / 10000000000000 : ℝ)
    hlog_24 hlog_25 (by norm_num [quadProd5Lo])

private lemma hlog_27 : (3373817410037 / 10000000000000 : ℝ) ≤ Real.log (220 / 157 : ℝ) ∧ Real.log (220 / 157 : ℝ) ≤ (843454352511 / 2500000000000 : ℝ) :=
  log_rat_bounds (220 / 157 : ℝ) (7 / 1577 : ℝ) (-1) (-2) (2) (3373817410037 / 10000000000000 : ℝ) (843454352511 / 2500000000000 : ℝ)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hlog_28 : (1739533071231 / 10000000000000 : ℝ) ≤ Real.log (119 / 100 : ℝ) ∧ Real.log (119 / 100 : ℝ) ≤ (869766535619 / 5000000000000 : ℝ) :=
  log_rat_bounds (119 / 100 : ℝ) (13 / 6413 : ℝ) (5) (-3) (0) (1739533071231 / 10000000000000 : ℝ) (869766535619 / 5000000000000 : ℝ)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hpsub_29 :
    IntervalIntegrable (fun t => Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1)) volume (37 / 25 : ℝ) (83 / 50 : ℝ) ∧
      (40837275303 / 10000000000000 : ℝ) ≤ ∫ t in (37 / 25 : ℝ)..(83 / 50 : ℝ), Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1) :=
  quad_prod5_sub (11 / 5 : ℝ) (220 / 157 : ℝ) (119 / 100 : ℝ) (37 / 25 : ℝ) (83 / 50 : ℝ) (157 / 100 : ℝ) (9 / 100 : ℝ)
    (100 / 157 : ℝ) (100 / 357 : ℝ) (100 / 257 : ℝ) (5868866961054280655345547 / 100000000000000000000000000 : ℝ) (-563646735048032436451462563803 / 14404593000000000000000000000000 : ℝ) (-292853888550399434151361974761405653 / 2074922994956490000000000000000000000 : ℝ) (111377419516974527728731784910206076334991 / 896652637460678734757100000000000000000000 : ℝ) (-375259502395390926759542308112488347129626317 / 4783672705554678028863325689000000000000000000 : ℝ) (275130263785449421942975461982776643702415828973797 / 6201617253185157862663661325884061930000000000000000 : ℝ)
    (412999007931379611427552746982776643702415828973797 / 15938156340685855707045609607522039160100000000000000 : ℝ) (-244589470000000000000 / 184381815917082355585083 : ℝ) (409287875000000000000 / 1659436343253741200265747 : ℝ) (-25700000000000000000 / 553145447751247066755249 : ℝ) (4000000000000000000 / 553145447751247066755249 : ℝ) (1301701 / 50000000 : ℝ)
    (3373817410037 / 10000000000000 : ℝ) (843454352511 / 2500000000000 : ℝ) (1739533071231 / 10000000000000 : ℝ) (869766535619 / 5000000000000 : ℝ) (40837275303 / 10000000000000 : ℝ)
    hlog_27 hlog_28 (by norm_num [quadProd5Lo])

private lemma hlog_30 : (2288415724287 / 10000000000000 : ℝ) ≤ Real.log (44 / 35 : ℝ) ∧ Real.log (44 / 35 : ℝ) ≤ (228841572429 / 1000000000000 : ℝ) :=
  log_rat_bounds (44 / 35 : ℝ) (1 / 351 : ℝ) (-2) (0) (1) (2288415724287 / 10000000000000 : ℝ) (228841572429 / 1000000000000 : ℝ)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hpsub_31 :
    IntervalIntegrable (fun t => Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1)) volume (83 / 50 : ℝ) (46 / 25 : ℝ) ∧
      (16629486183 / 5000000000000 : ℝ) ≤ ∫ t in (83 / 50 : ℝ)..(46 / 25 : ℝ), Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1) :=
  quad_prod5_sub (11 / 5 : ℝ) (44 / 35 : ℝ) (5 / 4 : ℝ) (83 / 50 : ℝ) (46 / 25 : ℝ) (7 / 4 : ℝ) (9 / 100 : ℝ)
    (4 / 7 : ℝ) (4 / 15 : ℝ) (4 / 11 : ℝ) (255322605800100330281559 / 5000000000000000000000000 : ℝ) (-744232109442491119270083 / 8750000000000000000000000 : ℝ) (-15691100989868332165109419 / 168437500000000000000000000 : ℝ) (7467436273920495927205680191 / 87545390625000000000000000000 : ℝ) (-259670002203136630730719284011 / 5055746308593750000000000000000 : ℝ) (2636819226863747173086970988077 / 97323116440429687500000000000000 : ℝ)
    (3961856666303747173086970988077 / 267638570211181640625000000000000 : ℝ) (-1712128 / 2363484375 : ℝ) (24408064 / 191442234375 : ℝ) (-1441792 / 63814078125 : ℝ) (1048576 / 319070390625 : ℝ) (743463 / 50000000 : ℝ)
    (2288415724287 / 10000000000000 : ℝ) (228841572429 / 1000000000000 : ℝ) (111571775657 / 500000000000 : ℝ) (278929439143 / 1250000000000 : ℝ) (16629486183 / 5000000000000 : ℝ)
    hlog_30 hlog_5 (by norm_num [quadProd5Lo])

private lemma hlog_32 : (163671696809 / 1250000000000 : ℝ) ≤ Real.log (220 / 193 : ℝ) ∧ Real.log (220 / 193 : ℝ) ≤ (1309373574477 / 10000000000000 : ℝ) :=
  log_rat_bounds (220 / 193 : ℝ) (23 / 3497 : ℝ) (-3) (2) (0) (163671696809 / 1250000000000 : ℝ) (1309373574477 / 10000000000000 : ℝ)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hlog_33 : (1350135686063 / 5000000000000 : ℝ) ≤ Real.log (131 / 100 : ℝ) ∧ Real.log (131 / 100 : ℝ) ≤ (540054274427 / 2000000000000 : ℝ) :=
  log_rat_bounds (131 / 100 : ℝ) (19 / 6269 : ℝ) (-5) (-1) (3) (1350135686063 / 5000000000000 : ℝ) (540054274427 / 2000000000000 : ℝ)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hpsub_34 :
    IntervalIntegrable (fun t => Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1)) volume (46 / 25 : ℝ) (101 / 50 : ℝ) ∧
      (10811051547 / 5000000000000 : ℝ) ≤ ∫ t in (46 / 25 : ℝ)..(101 / 50 : ℝ), Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1) :=
  quad_prod5_sub (11 / 5 : ℝ) (220 / 193 : ℝ) (131 / 100 : ℝ) (46 / 25 : ℝ) (101 / 50 : ℝ) (193 / 100 : ℝ) (9 / 100 : ℝ)
    (100 / 193 : ℝ) (100 / 393 : ℝ) (100 / 293 : ℝ) (220978998660314542872967 / 6250000000000000000000000 : ℝ) (-164817149798210976512371673983 / 1388984812500000000000000000000 : ℝ) (-18315855821637434761871245900063433 / 308684609496905625000000000000000000 : ℝ) (12220434979680901656696616862071733988851 / 205803952532973685857993750000000000000000 : ℝ) (-526387901971982358760413219786501212940119833 / 15245790102441138939674632025062500000000000000 : ℝ) (58144860378195871756600027493533425644545149213217 / 3388187345096569785985666811894069098125000000000000 : ℝ)
    (87823533864714850809982045306033425644545149213217 / 9927388921132949472938003758849622457506250000000000 : ℝ) (-349757030000000000000 / 836812275123462755218083 : ℝ) (525612875000000000000 / 7531310476111164796962747 : ℝ) (-29300000000000000000 / 2510436825370388265654249 : ℝ) (4000000000000000000 / 2510436825370388265654249 : ℝ) (888479 / 100000000 : ℝ)
    (163671696809 / 1250000000000 : ℝ) (1309373574477 / 10000000000000 : ℝ) (1350135686063 / 5000000000000 : ℝ) (540054274427 / 2000000000000 : ℝ) (10811051547 / 5000000000000 : ℝ)
    hlog_32 hlog_33 (by norm_num [quadProd5Lo])

private lemma hlog_35 : (10442353219 / 250000000000 : ℝ) ≤ Real.log (220 / 211 : ℝ) ∧ Real.log (220 / 211 : ℝ) ≤ (208847064383 / 5000000000000 : ℝ) :=
  log_rat_bounds (220 / 211 : ℝ) (1 / 2111 : ℝ) (-3) (-1) (2) (10442353219 / 250000000000 : ℝ) (208847064383 / 5000000000000 : ℝ)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hlog_36 : (3148107398397 / 10000000000000 : ℝ) ≤ Real.log (137 / 100 : ℝ) ∧ Real.log (137 / 100 : ℝ) ≤ (3148107398403 / 10000000000000 : ℝ) :=
  log_rat_bounds (137 / 100 : ℝ) (1 / 136 : ℝ) (-2) (3) (-1) (3148107398397 / 10000000000000 : ℝ) (3148107398403 / 10000000000000 : ℝ)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hpsub_37 :
    IntervalIntegrable (fun t => Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1)) volume (101 / 50 : ℝ) (11 / 5 : ℝ) ∧
      (7555544931 / 10000000000000 : ℝ) ≤ ∫ t in (101 / 50 : ℝ)..(11 / 5 : ℝ), Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1) :=
  quad_prod5_sub (11 / 5 : ℝ) (220 / 211 : ℝ) (137 / 100 : ℝ) (101 / 50 : ℝ) (11 / 5 : ℝ) (211 / 100 : ℝ) (9 / 100 : ℝ)
    (100 / 211 : ℝ) (100 / 411 : ℝ) (100 / 311 : ℝ) (32873649425408628389943 / 2500000000000000000000000 : ℝ) (-96597018088606605912604246903 / 674255775000000000000000000000 : ℝ) (-6387890298161177531763422104324937 / 181848340048340250000000000000000000 : ℝ) (6132330484616723774101571670677488584731 / 147134752142108631272932500000000000000000 : ℝ) (-313500458815821604254717799153036850018819017 / 13227527511334715375082711908025000000000000000 : ℝ) (39941655736035322216843963797261389453632003973257 / 3567494725395523919852323842658850037750000000000000 : ℝ)
    (60871590914155195080907037922261389453632003973257 / 11094908595980079390740727150669023617402500000000000 : ℝ) (-412569490000000000000 / 1634933644850401608165867 : ℝ) (589485875000000000000 / 14714402803653614473492803 : ℝ) (-31100000000000000000 / 4904800934551204824497601 : ℝ) (4000000000000000000 / 4904800934551204824497601 : ℝ) (550949 / 100000000 : ℝ)
    (10442353219 / 250000000000 : ℝ) (208847064383 / 5000000000000 : ℝ) (3148107398397 / 10000000000000 : ℝ) (3148107398403 / 10000000000000 : ℝ) (7555544931 / 10000000000000 : ℝ)
    hlog_35 hlog_36 (by norm_num [quadProd5Lo])

private lemma hpchain_38 :
    IntervalIntegrable (fun t => Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1)) volume (1 : ℝ) (83 / 50 : ℝ) ∧
      (30759248769 / 2500000000000 : ℝ) ≤ ∫ t in (1 : ℝ)..(83 / 50 : ℝ), Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1) :=
  chain4_int_lb hpsub_20 hpsub_23 hpsub_26 hpsub_29 (by norm_num)

private lemma hpchain_39 :
    IntervalIntegrable (fun t => Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1)) volume (1 : ℝ) (11 / 5 : ℝ) ∧
      (185473615467 / 10000000000000 : ℝ) ≤ ∫ t in (1 : ℝ)..(11 / 5 : ℝ), Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1) :=
  chain4_int_lb hpchain_38 hpsub_31 hpsub_34 hpsub_37 (by norm_num)

private lemma hlog_40 : (873808567623 / 250000000000 : ℝ) ≤ Real.log (2560000000 / 77674597 : ℝ) ∧ Real.log (2560000000 / 77674597 : ℝ) ≤ (34952342704927 / 10000000000000 : ℝ) :=
  log_rat_bounds (2560000000 / 77674597 : ℝ) (108357643 / 12691642357 : ℝ) (1) (4) (-1) (873808567623 / 250000000000 : ℝ) (34952342704927 / 10000000000000 : ℝ)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hterm_s0_41 :
    IntervalIntegrable (fun t => sigma0 t / ((5 : ℝ) * t) * Real.log (2560000000 / 77674597 : ℝ)) volume (1 : ℝ) (11 / 5 : ℝ) ∧
      (78264949637 / 5000000000000 : ℝ) ≤ ∫ t in (1 : ℝ)..(11 / 5 : ℝ), sigma0 t / ((5 : ℝ) * t) * Real.log (2560000000 / 77674597 : ℝ) :=
  bound_sigma0_term (5 : ℝ) (2560000000 / 77674597 : ℝ) (1 : ℝ) (11 / 5 : ℝ) (11 / 5 : ℝ)
    (343386816043 / 2000000000000 : ℝ) (1716934424407 / 10000000000000 : ℝ) (0 : ℝ) (7884573603639 / 10000000000000 : ℝ) (3942286801823 / 5000000000000 : ℝ) (185473615467 / 10000000000000 : ℝ) (873808567623 / 250000000000 : ℝ) (34952342704927 / 10000000000000 : ℝ) (78264949637 / 5000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hqchain_15 (by norm_num) hfga_16 hlog_17 hpchain_39.2 hlog_40
    (by norm_num) (by norm_num) (by norm_num)

private lemma hterm_42 :
    IntervalIntegrable (fun t => ind (5 / 2 : ℝ) (3 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) ^ (5 : ℕ) / (77674597 / 2500000 : ℝ))) volume (1 : ℝ) (11 / 5 : ℝ) ∧
      (0 : ℝ) ≤ ∫ t in (1 : ℝ)..(11 / 5 : ℝ), ind (5 / 2 : ℝ) (3 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) ^ (5 : ℕ) / (77674597 / 2500000 : ℝ)) :=
  bound_ind_div_zero (1 : ℝ) (11 / 5 : ℝ) (5 / 2 : ℝ) (3 : ℝ) (fun t => (5 : ℝ) * t) (fun t => (t + 1) ^ (5 : ℕ) / (77674597 / 2500000 : ℝ)) (by norm_num) (Or.inr (by norm_num))

private lemma hlog_44 : (197272430263 / 312500000000 : ℝ) ≤ Real.log (47 / 25 : ℝ) ∧ Real.log (47 / 25 : ℝ) ≤ (6312717768421 / 10000000000000 : ℝ) :=
  log_rat_bounds (47 / 25 : ℝ) (1 / 751 : ℝ) (-3) (1) (1) (197272430263 / 312500000000 : ℝ) (6312717768421 / 10000000000000 : ℝ)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hlog_45 : (1611193491429 / 10000000000000 : ℝ) ≤ Real.log (168 / 143 : ℝ) ∧ Real.log (168 / 143 : ℝ) ≤ (805596745719 / 5000000000000 : ℝ) :=
  log_rat_bounds (168 / 143 : ℝ) (9 / 7159 : ℝ) (-6) (1) (2) (1611193491429 / 10000000000000 : ℝ) (805596745719 / 5000000000000 : ℝ)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hlog_46 : (8620105249607 / 10000000000000 : ℝ) ≤ Real.log (5683 / 2400 : ℝ) ∧ Real.log (5683 / 2400 : ℝ) ≤ (4310052624807 / 5000000000000 : ℝ) :=
  log_rat_bounds (5683 / 2400 : ℝ) (29 / 5654 : ℝ) (-5) (1) (2) (8620105249607 / 10000000000000 : ℝ) (4310052624807 / 5000000000000 : ℝ)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hqsub_47 :
    IntervalIntegrable (fun t => Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t)) volume (1573 / 1200 : ℝ) (57 / 40 : ℝ) ∧
      (719493052989 / 10000000000000 : ℝ) ≤ ∫ t in (1573 / 1200 : ℝ)..(57 / 40 : ℝ), Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (1573 / 1200 : ℝ)..(57 / 40 : ℝ), Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ≤ (719493058001 / 10000000000000 : ℝ) :=
  quad_log_div_sub (1 : ℝ) (1 : ℝ) (0 : ℝ) (1 : ℝ) (1573 / 1200 : ℝ) (57 / 40 : ℝ) (3283 / 2400 : ℝ) (137 / 2400 : ℝ)
    (5683 / 2400 : ℝ) (3283 / 2400 : ℝ) (2400 / 5683 : ℝ) (2400 / 3283 : ℝ) (2400 / 3283 : ℝ) (8620105249607 / 10000000000000 : ℝ) (4310052624807 / 5000000000000 : ℝ) (719493052989 / 10000000000000 : ℝ) (719493058001 / 10000000000000 : ℝ)
    hlog_46 (by norm_num [quadLogLo, quadLogHi])

private lemma hlog_48 : (9092661169367 / 10000000000000 : ℝ) ≤ Real.log (993 / 400 : ℝ) ∧ Real.log (993 / 400 : ℝ) ≤ (284145661543 / 312500000000 : ℝ) :=
  log_rat_bounds (993 / 400 : ℝ) (433 / 160433 : ℝ) (3) (-4) (2) (9092661169367 / 10000000000000 : ℝ) (284145661543 / 312500000000 : ℝ)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hqsub_49 :
    IntervalIntegrable (fun t => Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t)) volume (57 / 40 : ℝ) (77 / 50 : ℝ) ∧
      (176346237967 / 2500000000000 : ℝ) ≤ ∫ t in (57 / 40 : ℝ)..(77 / 50 : ℝ), Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (57 / 40 : ℝ)..(77 / 50 : ℝ), Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ≤ (176346238723 / 2500000000000 : ℝ) :=
  quad_log_div_sub (1 : ℝ) (1 : ℝ) (0 : ℝ) (1 : ℝ) (57 / 40 : ℝ) (77 / 50 : ℝ) (593 / 400 : ℝ) (23 / 400 : ℝ)
    (993 / 400 : ℝ) (593 / 400 : ℝ) (400 / 993 : ℝ) (400 / 593 : ℝ) (400 / 593 : ℝ) (9092661169367 / 10000000000000 : ℝ) (284145661543 / 312500000000 : ℝ) (176346237967 / 2500000000000 : ℝ) (176346238723 / 2500000000000 : ℝ)
    hlog_48 (by norm_num [quadLogLo, quadLogHi])

private lemma hqchain_50 :
    IntervalIntegrable (fun t => Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t)) volume (1573 / 1200 : ℝ) (77 / 50 : ℝ) ∧
      (1424878004857 / 10000000000000 : ℝ) ≤ ∫ t in (1573 / 1200 : ℝ)..(77 / 50 : ℝ), Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (1573 / 1200 : ℝ)..(77 / 50 : ℝ), Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ≤ (1424878012893 / 10000000000000 : ℝ) :=
  chain_int_bounds hqsub_47 hqsub_49 (by norm_num)

private lemma hlog_51 : (793913960767 / 5000000000000 : ℝ) ≤ Real.log (2813 / 2400 : ℝ) ∧ Real.log (2813 / 2400 : ℝ) ≤ (793913960771 / 5000000000000 : ℝ) :=
  log_rat_bounds (2813 / 2400 : ℝ) (1 / 11251 : ℝ) (-6) (1) (2) (793913960767 / 5000000000000 : ℝ) (793913960771 / 5000000000000 : ℝ)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hqsub_52 :
    IntervalIntegrable (fun t => Real.log ((127 / 50 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t)) volume (1573 / 1200 : ℝ) (57 / 40 : ℝ) ∧
      (132833260877 / 10000000000000 : ℝ) ≤ ∫ t in (1573 / 1200 : ℝ)..(57 / 40 : ℝ), Real.log ((127 / 50 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (1573 / 1200 : ℝ)..(57 / 40 : ℝ), Real.log ((127 / 50 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ≤ (2075519877 / 156250000000 : ℝ) :=
  quad_log_div_sub (127 / 50 : ℝ) (-1 : ℝ) (0 : ℝ) (1 : ℝ) (1573 / 1200 : ℝ) (57 / 40 : ℝ) (3283 / 2400 : ℝ) (137 / 2400 : ℝ)
    (2813 / 2400 : ℝ) (3283 / 2400 : ℝ) (-2400 / 2813 : ℝ) (2400 / 3283 : ℝ) (2400 / 2813 : ℝ) (793913960767 / 5000000000000 : ℝ) (793913960771 / 5000000000000 : ℝ) (132833260877 / 10000000000000 : ℝ) (2075519877 / 156250000000 : ℝ)
    hlog_51 (by norm_num [quadLogLo, quadLogHi])

private lemma hlog_53 : (279538159689 / 5000000000000 : ℝ) ≤ Real.log (423 / 400 : ℝ) ∧ Real.log (423 / 400 : ℝ) ≤ (139769079847 / 2500000000000 : ℝ) :=
  log_rat_bounds (423 / 400 : ℝ) (1 / 751 : ℝ) (-7) (3) (1) (279538159689 / 5000000000000 : ℝ) (139769079847 / 2500000000000 : ℝ)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hqsub_54 :
    IntervalIntegrable (fun t => Real.log ((127 / 50 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t)) volume (57 / 40 : ℝ) (77 / 50 : ℝ) ∧
      (10888361913 / 2500000000000 : ℝ) ≤ ∫ t in (57 / 40 : ℝ)..(77 / 50 : ℝ), Real.log ((127 / 50 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (57 / 40 : ℝ)..(77 / 50 : ℝ), Real.log ((127 / 50 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ≤ (10888366931 / 2500000000000 : ℝ) :=
  quad_log_div_sub (127 / 50 : ℝ) (-1 : ℝ) (0 : ℝ) (1 : ℝ) (57 / 40 : ℝ) (77 / 50 : ℝ) (593 / 400 : ℝ) (23 / 400 : ℝ)
    (423 / 400 : ℝ) (593 / 400 : ℝ) (-400 / 423 : ℝ) (400 / 593 : ℝ) (400 / 423 : ℝ) (279538159689 / 5000000000000 : ℝ) (139769079847 / 2500000000000 : ℝ) (10888361913 / 2500000000000 : ℝ) (10888366931 / 2500000000000 : ℝ)
    hlog_53 (by norm_num [quadLogLo, quadLogHi])

private lemma hqchain_55 :
    IntervalIntegrable (fun t => Real.log ((127 / 50 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t)) volume (1573 / 1200 : ℝ) (77 / 50 : ℝ) ∧
      (176386708529 / 10000000000000 : ℝ) ≤ ∫ t in (1573 / 1200 : ℝ)..(77 / 50 : ℝ), Real.log ((127 / 50 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (1573 / 1200 : ℝ)..(77 / 50 : ℝ), Real.log ((127 / 50 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ≤ (44096684963 / 2500000000000 : ℝ) :=
  chain_int_bounds hqsub_52 hqsub_54 (by norm_num)

private lemma hact_tl_56 :
    IntervalIntegrable (fun t => Real.log ((t + 1) / ((47 / 25 : ℝ) * ((127 / 50 : ℝ) - t))) / ((5 : ℝ) * t)) volume (1573 / 1200 : ℝ) (77 / 50 : ℝ) ∧
      (9255611473 / 2000000000000 : ℝ) ≤ ∫ t in (1573 / 1200 : ℝ)..(77 / 50 : ℝ), Real.log ((t + 1) / ((47 / 25 : ℝ) * ((127 / 50 : ℝ) - t))) / ((5 : ℝ) * t) :=
  active_t_lin (5 : ℝ) (47 / 25 : ℝ) (127 / 50 : ℝ) (1573 / 1200 : ℝ) (77 / 50 : ℝ) (168 / 143 : ℝ) (197272430263 / 312500000000 : ℝ) (6312717768421 / 10000000000000 : ℝ) (1611193491429 / 10000000000000 : ℝ) (805596745719 / 5000000000000 : ℝ)
    (1424878004857 / 10000000000000 : ℝ) (1424878012893 / 10000000000000 : ℝ) (176386708529 / 10000000000000 : ℝ) (44096684963 / 2500000000000 : ℝ) (9255611473 / 2000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog_44 hlog_45 hqchain_50 hqchain_55 (by norm_num)

private lemma hterm_43 :
    IntervalIntegrable (fun t => ind (1573 / 1200 : ℝ) (77 / 50 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) / ((47 / 25 : ℝ) * ((127 / 50 : ℝ) - t)))) volume (1 : ℝ) (11 / 5 : ℝ) ∧
      (9255611473 / 2000000000000 : ℝ) ≤ ∫ t in (1 : ℝ)..(11 / 5 : ℝ), ind (1573 / 1200 : ℝ) (77 / 50 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) / ((47 / 25 : ℝ) * ((127 / 50 : ℝ) - t))) :=
  bound_ind_div_active (1 : ℝ) (11 / 5 : ℝ) (1573 / 1200 : ℝ) (77 / 50 : ℝ) (1573 / 1200 : ℝ) (77 / 50 : ℝ) (9255611473 / 2000000000000 : ℝ)
    (fun t => (5 : ℝ) * t) (fun t => (t + 1) / ((47 / 25 : ℝ) * ((127 / 50 : ℝ) - t)))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (Or.inr rfl) (Or.inr rfl) hact_tl_56

private lemma hlog_58 : (1788372221357 / 5000000000000 : ℝ) ≤ Real.log (143 / 100 : ℝ) ∧ Real.log (143 / 100 : ℝ) ≤ (1788372221361 / 5000000000000 : ℝ) :=
  log_rat_bounds (143 / 100 : ℝ) (7 / 2567 : ℝ) (6) (-2) (-1) (1788372221357 / 5000000000000 : ℝ) (1788372221361 / 5000000000000 : ℝ)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hlog_59 : (1444025185981 / 5000000000000 : ℝ) ≤ Real.log (594 / 445 : ℝ) ∧ Real.log (594 / 445 : ℝ) ≤ (1444025185983 / 5000000000000 : ℝ) :=
  log_rat_bounds (594 / 445 : ℝ) (1 / 1781 : ℝ) (2) (-1) (0) (1444025185981 / 5000000000000 : ℝ) (1444025185983 / 5000000000000 : ℝ)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hlog_60 : (10076199341187 / 10000000000000 : ℝ) ≤ Real.log (14791 / 5400 : ℝ) ∧ Real.log (14791 / 5400 : ℝ) ≤ (10076199341193 / 10000000000000 : ℝ) :=
  log_rat_bounds (14791 / 5400 : ℝ) (211 / 29371 : ℝ) (-1) (3) (-1) (10076199341187 / 10000000000000 : ℝ) (10076199341193 / 10000000000000 : ℝ)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hqsub_61 :
    IntervalIntegrable (fun t => Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t)) volume (89 / 54 : ℝ) (183 / 100 : ℝ) ∧
      (263453300349 / 2500000000000 : ℝ) ≤ ∫ t in (89 / 54 : ℝ)..(183 / 100 : ℝ), Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (89 / 54 : ℝ)..(183 / 100 : ℝ), Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ≤ (42152529047 / 400000000000 : ℝ) :=
  quad_log_div_sub (1 : ℝ) (1 : ℝ) (0 : ℝ) (1 : ℝ) (89 / 54 : ℝ) (183 / 100 : ℝ) (9391 / 5400 : ℝ) (491 / 5400 : ℝ)
    (14791 / 5400 : ℝ) (9391 / 5400 : ℝ) (5400 / 14791 : ℝ) (5400 / 9391 : ℝ) (5400 / 9391 : ℝ) (10076199341187 / 10000000000000 : ℝ) (10076199341193 / 10000000000000 : ℝ) (263453300349 / 2500000000000 : ℝ) (42152529047 / 400000000000 : ℝ)
    hlog_60 (by norm_num [quadLogLo, quadLogHi])

private lemma hlog_62 : (10724394143637 / 10000000000000 : ℝ) ≤ Real.log (1169 / 400 : ℝ) ∧ Real.log (1169 / 400 : ℝ) ≤ (2681098535911 / 2500000000000 : ℝ) :=
  log_rat_bounds (1169 / 400 : ℝ) (17 / 2321 : ℝ) (3) (2) (-2) (10724394143637 / 10000000000000 : ℝ) (2681098535911 / 2500000000000 : ℝ)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hqsub_63 :
    IntervalIntegrable (fun t => Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t)) volume (183 / 100 : ℝ) (403 / 200 : ℝ) ∧
      (1032143576981 / 10000000000000 : ℝ) ≤ ∫ t in (183 / 100 : ℝ)..(403 / 200 : ℝ), Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (183 / 100 : ℝ)..(403 / 200 : ℝ), Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ≤ (1032143590953 / 10000000000000 : ℝ) :=
  quad_log_div_sub (1 : ℝ) (1 : ℝ) (0 : ℝ) (1 : ℝ) (183 / 100 : ℝ) (403 / 200 : ℝ) (769 / 400 : ℝ) (37 / 400 : ℝ)
    (1169 / 400 : ℝ) (769 / 400 : ℝ) (400 / 1169 : ℝ) (400 / 769 : ℝ) (400 / 769 : ℝ) (10724394143637 / 10000000000000 : ℝ) (2681098535911 / 2500000000000 : ℝ) (1032143576981 / 10000000000000 : ℝ) (1032143590953 / 10000000000000 : ℝ)
    hlog_62 (by norm_num [quadLogLo, quadLogHi])

private lemma hlog_64 : (5669092722011 / 5000000000000 : ℝ) ≤ Real.log (1243 / 400 : ℝ) ∧ Real.log (1243 / 400 : ℝ) ≤ (177159147563 / 156250000000 : ℝ) :=
  log_rat_bounds (1243 / 400 : ℝ) (683 / 200683 : ℝ) (1) (-4) (3) (5669092722011 / 5000000000000 : ℝ) (177159147563 / 156250000000 : ℝ)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hqsub_65 :
    IntervalIntegrable (fun t => Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t)) volume (403 / 200 : ℝ) (11 / 5 : ℝ) ∧
      (124426598437 / 1250000000000 : ℝ) ≤ ∫ t in (403 / 200 : ℝ)..(11 / 5 : ℝ), Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (403 / 200 : ℝ)..(11 / 5 : ℝ), Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ≤ (995412794903 / 10000000000000 : ℝ) :=
  quad_log_div_sub (1 : ℝ) (1 : ℝ) (0 : ℝ) (1 : ℝ) (403 / 200 : ℝ) (11 / 5 : ℝ) (843 / 400 : ℝ) (37 / 400 : ℝ)
    (1243 / 400 : ℝ) (843 / 400 : ℝ) (400 / 1243 : ℝ) (400 / 843 : ℝ) (400 / 843 : ℝ) (5669092722011 / 5000000000000 : ℝ) (177159147563 / 156250000000 : ℝ) (124426598437 / 1250000000000 : ℝ) (995412794903 / 10000000000000 : ℝ)
    hlog_64 (by norm_num [quadLogLo, quadLogHi])

private lemma hqchain_66 :
    IntervalIntegrable (fun t => Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t)) volume (89 / 54 : ℝ) (403 / 200 : ℝ) ∧
      (2085956778377 / 10000000000000 : ℝ) ≤ ∫ t in (89 / 54 : ℝ)..(403 / 200 : ℝ), Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (89 / 54 : ℝ)..(403 / 200 : ℝ), Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ≤ (260744602141 / 1250000000000 : ℝ) :=
  chain_int_bounds hqsub_61 hqsub_63 (by norm_num)

private lemma hqchain_67 :
    IntervalIntegrable (fun t => Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t)) volume (89 / 54 : ℝ) (11 / 5 : ℝ) ∧
      (3081369565873 / 10000000000000 : ℝ) ≤ ∫ t in (89 / 54 : ℝ)..(11 / 5 : ℝ), Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (89 / 54 : ℝ)..(11 / 5 : ℝ), Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ≤ (3081369612031 / 10000000000000 : ℝ) :=
  chain_int_bounds hqchain_66 hqsub_65 (by norm_num)

private lemma hlog_68 : (2829198824933 / 5000000000000 : ℝ) ≤ Real.log (9509 / 5400 : ℝ) ∧ Real.log (9509 / 5400 : ℝ) ≤ (1414599412469 / 2500000000000 : ℝ) :=
  log_rat_bounds (9509 / 5400 : ℝ) (269 / 304019 : ℝ) (-7) (2) (2) (2829198824933 / 5000000000000 : ℝ) (1414599412469 / 2500000000000 : ℝ)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hqsub_69 :
    IntervalIntegrable (fun t => Real.log ((7 / 2 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t)) volume (89 / 54 : ℝ) (183 / 100 : ℝ) ∧
      (29635287929 / 500000000000 : ℝ) ≤ ∫ t in (89 / 54 : ℝ)..(183 / 100 : ℝ), Real.log ((7 / 2 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (89 / 54 : ℝ)..(183 / 100 : ℝ), Real.log ((7 / 2 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ≤ (592705781861 / 10000000000000 : ℝ) :=
  quad_log_div_sub (7 / 2 : ℝ) (-1 : ℝ) (0 : ℝ) (1 : ℝ) (89 / 54 : ℝ) (183 / 100 : ℝ) (9391 / 5400 : ℝ) (491 / 5400 : ℝ)
    (9509 / 5400 : ℝ) (9391 / 5400 : ℝ) (-5400 / 9509 : ℝ) (5400 / 9391 : ℝ) (5400 / 9391 : ℝ) (2829198824933 / 5000000000000 : ℝ) (1414599412469 / 2500000000000 : ℝ) (29635287929 / 500000000000 : ℝ) (592705781861 / 10000000000000 : ℝ)
    hlog_68 (by norm_num [quadLogLo, quadLogHi])

private lemma hlog_70 : (4558413154329 / 10000000000000 : ℝ) ≤ Real.log (631 / 400 : ℝ) ∧ Real.log (631 / 400 : ℝ) ≤ (911682630867 / 2000000000000 : ℝ) :=
  log_rat_bounds (631 / 400 : ℝ) (3 / 628 : ℝ) (-4) (0) (2) (4558413154329 / 10000000000000 : ℝ) (911682630867 / 2000000000000 : ℝ)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hqsub_71 :
    IntervalIntegrable (fun t => Real.log ((7 / 2 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t)) volume (183 / 100 : ℝ) (403 / 200 : ℝ) ∧
      (439343952453 / 10000000000000 : ℝ) ≤ ∫ t in (183 / 100 : ℝ)..(403 / 200 : ℝ), Real.log ((7 / 2 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (183 / 100 : ℝ)..(403 / 200 : ℝ), Real.log ((7 / 2 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ≤ (439343992433 / 10000000000000 : ℝ) :=
  quad_log_div_sub (7 / 2 : ℝ) (-1 : ℝ) (0 : ℝ) (1 : ℝ) (183 / 100 : ℝ) (403 / 200 : ℝ) (769 / 400 : ℝ) (37 / 400 : ℝ)
    (631 / 400 : ℝ) (769 / 400 : ℝ) (-400 / 631 : ℝ) (400 / 769 : ℝ) (400 / 631 : ℝ) (4558413154329 / 10000000000000 : ℝ) (911682630867 / 2000000000000 : ℝ) (439343952453 / 10000000000000 : ℝ) (439343992433 / 10000000000000 : ℝ)
    hlog_70 (by norm_num [quadLogLo, quadLogHi])

private lemma hlog_72 : (331100692819 / 1000000000000 : ℝ) ≤ Real.log (557 / 400 : ℝ) ∧ Real.log (557 / 400 : ℝ) ≤ (827751732049 / 2500000000000 : ℝ) :=
  log_rat_bounds (557 / 400 : ℝ) (13 / 10013 : ℝ) (-1) (-2) (2) (331100692819 / 1000000000000 : ℝ) (827751732049 / 2500000000000 : ℝ)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hqsub_73 :
    IntervalIntegrable (fun t => Real.log ((7 / 2 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t)) volume (403 / 200 : ℝ) (11 / 5 : ℝ) ∧
      (291040406157 / 10000000000000 : ℝ) ≤ ∫ t in (403 / 200 : ℝ)..(11 / 5 : ℝ), Real.log ((7 / 2 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (403 / 200 : ℝ)..(11 / 5 : ℝ), Real.log ((7 / 2 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ≤ (72760120477 / 2500000000000 : ℝ) :=
  quad_log_div_sub (7 / 2 : ℝ) (-1 : ℝ) (0 : ℝ) (1 : ℝ) (403 / 200 : ℝ) (11 / 5 : ℝ) (843 / 400 : ℝ) (37 / 400 : ℝ)
    (557 / 400 : ℝ) (843 / 400 : ℝ) (-400 / 557 : ℝ) (400 / 843 : ℝ) (400 / 557 : ℝ) (331100692819 / 1000000000000 : ℝ) (827751732049 / 2500000000000 : ℝ) (291040406157 / 10000000000000 : ℝ) (72760120477 / 2500000000000 : ℝ)
    hlog_72 (by norm_num [quadLogLo, quadLogHi])

private lemma hqchain_74 :
    IntervalIntegrable (fun t => Real.log ((7 / 2 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t)) volume (89 / 54 : ℝ) (403 / 200 : ℝ) ∧
      (1032049711033 / 10000000000000 : ℝ) ≤ ∫ t in (89 / 54 : ℝ)..(403 / 200 : ℝ), Real.log ((7 / 2 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (89 / 54 : ℝ)..(403 / 200 : ℝ), Real.log ((7 / 2 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ≤ (516024887147 / 5000000000000 : ℝ) :=
  chain_int_bounds hqsub_69 hqsub_71 (by norm_num)

private lemma hqchain_75 :
    IntervalIntegrable (fun t => Real.log ((7 / 2 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t)) volume (89 / 54 : ℝ) (11 / 5 : ℝ) ∧
      (132309011719 / 1000000000000 : ℝ) ≤ ∫ t in (89 / 54 : ℝ)..(11 / 5 : ℝ), Real.log ((7 / 2 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (89 / 54 : ℝ)..(11 / 5 : ℝ), Real.log ((7 / 2 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ≤ (661545128101 / 5000000000000 : ℝ) :=
  chain_int_bounds hqchain_74 hqsub_73 (by norm_num)

private lemma hact_tl_76 :
    IntervalIntegrable (fun t => Real.log ((t + 1) / ((143 / 100 : ℝ) * ((7 / 2 : ℝ) - t))) / ((5 : ℝ) * t)) volume (89 / 54 : ℝ) (11 / 5 : ℝ) ∧
      (145059499569 / 10000000000000 : ℝ) ≤ ∫ t in (89 / 54 : ℝ)..(11 / 5 : ℝ), Real.log ((t + 1) / ((143 / 100 : ℝ) * ((7 / 2 : ℝ) - t))) / ((5 : ℝ) * t) :=
  active_t_lin (5 : ℝ) (143 / 100 : ℝ) (7 / 2 : ℝ) (89 / 54 : ℝ) (11 / 5 : ℝ) (594 / 445 : ℝ) (1788372221357 / 5000000000000 : ℝ) (1788372221361 / 5000000000000 : ℝ) (1444025185981 / 5000000000000 : ℝ) (1444025185983 / 5000000000000 : ℝ)
    (3081369565873 / 10000000000000 : ℝ) (3081369612031 / 10000000000000 : ℝ) (132309011719 / 1000000000000 : ℝ) (661545128101 / 5000000000000 : ℝ) (145059499569 / 10000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog_58 hlog_59 hqchain_67 hqchain_75 (by norm_num)

private lemma hterm_57 :
    IntervalIntegrable (fun t => ind (89 / 54 : ℝ) (5 / 2 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) / ((143 / 100 : ℝ) * ((7 / 2 : ℝ) - t)))) volume (1 : ℝ) (11 / 5 : ℝ) ∧
      (145059499569 / 10000000000000 : ℝ) ≤ ∫ t in (1 : ℝ)..(11 / 5 : ℝ), ind (89 / 54 : ℝ) (5 / 2 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) / ((143 / 100 : ℝ) * ((7 / 2 : ℝ) - t))) :=
  bound_ind_div_active (1 : ℝ) (11 / 5 : ℝ) (89 / 54 : ℝ) (5 / 2 : ℝ) (89 / 54 : ℝ) (11 / 5 : ℝ) (145059499569 / 10000000000000 : ℝ)
    (fun t => (5 : ℝ) * t) (fun t => (t + 1) / ((143 / 100 : ℝ) * ((7 / 2 : ℝ) - t)))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (Or.inr rfl) (Or.inl rfl) hact_tl_76

private lemma hlog_78 : (262364264467 / 1000000000000 : ℝ) ≤ Real.log (13 / 10 : ℝ) ∧ Real.log (13 / 10 : ℝ) ≤ (65591066117 / 250000000000 : ℝ) :=
  log_rat_bounds (13 / 10 : ℝ) (1 / 649 : ℝ) (1) (4) (-3) (262364264467 / 1000000000000 : ℝ) (65591066117 / 250000000000 : ℝ)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hlog_79 : (886047199529 / 2500000000000 : ℝ) ≤ Real.log (506 / 355 : ℝ) ∧ Real.log (506 / 355 : ℝ) ≤ (886047199531 / 2500000000000 : ℝ) :=
  log_rat_bounds (506 / 355 : ℝ) (5 / 4549 : ℝ) (6) (-2) (-1) (886047199529 / 2500000000000 : ℝ) (886047199531 / 2500000000000 : ℝ)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hlog_80 : (9752157003787 / 10000000000000 : ℝ) ≤ Real.log (6099 / 2300 : ℝ) ∧ Real.log (6099 / 2300 : ℝ) ≤ (2438039250949 / 2500000000000 : ℝ) :=
  log_rat_bounds (6099 / 2300 : ℝ) (1313 / 145063 : ℝ) (-4) (-1) (3) (9752157003787 / 10000000000000 : ℝ) (2438039250949 / 2500000000000 : ℝ)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hqsub_81 :
    IntervalIntegrable (fun t => Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t)) volume (71 / 46 : ℝ) (44 / 25 : ℝ) ∧
      (319669902297 / 2500000000000 : ℝ) ≤ ∫ t in (71 / 46 : ℝ)..(44 / 25 : ℝ), Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (71 / 46 : ℝ)..(44 / 25 : ℝ), Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ≤ (159834966151 / 1250000000000 : ℝ) :=
  quad_log_div_sub (1 : ℝ) (1 : ℝ) (0 : ℝ) (1 : ℝ) (71 / 46 : ℝ) (44 / 25 : ℝ) (3799 / 2300 : ℝ) (249 / 2300 : ℝ)
    (6099 / 2300 : ℝ) (3799 / 2300 : ℝ) (2300 / 6099 : ℝ) (2300 / 3799 : ℝ) (2300 / 3799 : ℝ) (9752157003787 / 10000000000000 : ℝ) (2438039250949 / 2500000000000 : ℝ) (319669902297 / 2500000000000 : ℝ) (159834966151 / 1250000000000 : ℝ)
    hlog_80 (by norm_num [quadLogLo, quadLogHi])

private lemma hlog_82 : (1054312029771 / 1000000000000 : ℝ) ≤ Real.log (287 / 100 : ℝ) ∧ Real.log (287 / 100 : ℝ) ≤ (10543120297719 / 10000000000000 : ℝ) :=
  log_rat_bounds (287 / 100 : ℝ) (23 / 5143 : ℝ) (7) (-2) (-1) (1054312029771 / 1000000000000 : ℝ) (10543120297719 / 10000000000000 : ℝ)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hqsub_83 :
    IntervalIntegrable (fun t => Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t)) volume (44 / 25 : ℝ) (99 / 50 : ℝ) ∧
      (1240625681543 / 10000000000000 : ℝ) ≤ ∫ t in (44 / 25 : ℝ)..(99 / 50 : ℝ), Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (44 / 25 : ℝ)..(99 / 50 : ℝ), Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ≤ (620312869221 / 5000000000000 : ℝ) :=
  quad_log_div_sub (1 : ℝ) (1 : ℝ) (0 : ℝ) (1 : ℝ) (44 / 25 : ℝ) (99 / 50 : ℝ) (187 / 100 : ℝ) (11 / 100 : ℝ)
    (287 / 100 : ℝ) (187 / 100 : ℝ) (100 / 287 : ℝ) (100 / 187 : ℝ) (100 / 187 : ℝ) (1054312029771 / 1000000000000 : ℝ) (10543120297719 / 10000000000000 : ℝ) (1240625681543 / 10000000000000 : ℝ) (620312869221 / 5000000000000 : ℝ)
    hlog_82 (by norm_num [quadLogLo, quadLogHi])

private lemma hlog_84 : (11281710909091 / 10000000000000 : ℝ) ≤ Real.log (309 / 100 : ℝ) ∧ Real.log (309 / 100 : ℝ) ≤ (11281710909101 / 10000000000000 : ℝ) :=
  log_rat_bounds (309 / 100 : ℝ) (29 / 50029 : ℝ) (1) (-4) (3) (11281710909091 / 10000000000000 : ℝ) (11281710909101 / 10000000000000 : ℝ)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hqsub_85 :
    IntervalIntegrable (fun t => Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t)) volume (99 / 50 : ℝ) (11 / 5 : ℝ) ∧
      (148470676741 / 1250000000000 : ℝ) ≤ ∫ t in (99 / 50 : ℝ)..(11 / 5 : ℝ), Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (99 / 50 : ℝ)..(11 / 5 : ℝ), Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ≤ (148470680039 / 1250000000000 : ℝ) :=
  quad_log_div_sub (1 : ℝ) (1 : ℝ) (0 : ℝ) (1 : ℝ) (99 / 50 : ℝ) (11 / 5 : ℝ) (209 / 100 : ℝ) (11 / 100 : ℝ)
    (309 / 100 : ℝ) (209 / 100 : ℝ) (100 / 309 : ℝ) (100 / 209 : ℝ) (100 / 209 : ℝ) (11281710909091 / 10000000000000 : ℝ) (11281710909101 / 10000000000000 : ℝ) (148470676741 / 1250000000000 : ℝ) (148470680039 / 1250000000000 : ℝ)
    hlog_84 (by norm_num [quadLogLo, quadLogHi])

private lemma hqchain_86 :
    IntervalIntegrable (fun t => Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t)) volume (71 / 46 : ℝ) (99 / 50 : ℝ) ∧
      (2519305290731 / 10000000000000 : ℝ) ≤ ∫ t in (71 / 46 : ℝ)..(99 / 50 : ℝ), Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (71 / 46 : ℝ)..(99 / 50 : ℝ), Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ≤ (50386109353 / 200000000000 : ℝ) :=
  chain_int_bounds hqsub_81 hqsub_83 (by norm_num)

private lemma hqchain_87 :
    IntervalIntegrable (fun t => Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t)) volume (71 / 46 : ℝ) (11 / 5 : ℝ) ∧
      (3707070704659 / 10000000000000 : ℝ) ≤ ∫ t in (71 / 46 : ℝ)..(11 / 5 : ℝ), Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (71 / 46 : ℝ)..(11 / 5 : ℝ), Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ≤ (1853535453981 / 5000000000000 : ℝ) :=
  chain_int_bounds hqchain_86 hqsub_85 (by norm_num)

private lemma hlog_88 : (6142451264413 / 10000000000000 : ℝ) ≤ Real.log (4251 / 2300 : ℝ) ∧ Real.log (4251 / 2300 : ℝ) ≤ (6142451264417 / 10000000000000 : ℝ) :=
  log_rat_bounds (4251 / 2300 : ℝ) (37 / 2797 : ℝ) (0) (2) (-1) (6142451264413 / 10000000000000 : ℝ) (6142451264417 / 10000000000000 : ℝ)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hqsub_89 :
    IntervalIntegrable (fun t => Real.log ((7 / 2 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t)) volume (71 / 46 : ℝ) (44 / 25 : ℝ) ∧
      (25227593173 / 312500000000 : ℝ) ≤ ∫ t in (71 / 46 : ℝ)..(44 / 25 : ℝ), Real.log ((7 / 2 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (71 / 46 : ℝ)..(44 / 25 : ℝ), Real.log ((7 / 2 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ≤ (807283095601 / 10000000000000 : ℝ) :=
  quad_log_div_sub (7 / 2 : ℝ) (-1 : ℝ) (0 : ℝ) (1 : ℝ) (71 / 46 : ℝ) (44 / 25 : ℝ) (3799 / 2300 : ℝ) (249 / 2300 : ℝ)
    (4251 / 2300 : ℝ) (3799 / 2300 : ℝ) (-2300 / 4251 : ℝ) (2300 / 3799 : ℝ) (2300 / 3799 : ℝ) (6142451264413 / 10000000000000 : ℝ) (6142451264417 / 10000000000000 : ℝ) (25227593173 / 312500000000 : ℝ) (807283095601 / 10000000000000 : ℝ)
    hlog_88 (by norm_num [quadLogLo, quadLogHi])

private lemma hlog_90 : (2442900074091 / 5000000000000 : ℝ) ≤ Real.log (163 / 100 : ℝ) ∧ Real.log (163 / 100 : ℝ) ≤ (4885800148191 / 10000000000000 : ℝ) :=
  log_rat_bounds (163 / 100 : ℝ) (1 / 325 : ℝ) (-1) (4) (-2) (2442900074091 / 5000000000000 : ℝ) (4885800148191 / 10000000000000 : ℝ)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hqsub_91 :
    IntervalIntegrable (fun t => Real.log ((7 / 2 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t)) volume (44 / 25 : ℝ) (99 / 50 : ℝ) ∧
      (576129653259 / 10000000000000 : ℝ) ≤ ∫ t in (44 / 25 : ℝ)..(99 / 50 : ℝ), Real.log ((7 / 2 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (44 / 25 : ℝ)..(99 / 50 : ℝ), Real.log ((7 / 2 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ≤ (288064884083 / 5000000000000 : ℝ) :=
  quad_log_div_sub (7 / 2 : ℝ) (-1 : ℝ) (0 : ℝ) (1 : ℝ) (44 / 25 : ℝ) (99 / 50 : ℝ) (187 / 100 : ℝ) (11 / 100 : ℝ)
    (163 / 100 : ℝ) (187 / 100 : ℝ) (-100 / 163 : ℝ) (100 / 187 : ℝ) (100 / 163 : ℝ) (2442900074091 / 5000000000000 : ℝ) (4885800148191 / 10000000000000 : ℝ) (576129653259 / 10000000000000 : ℝ) (288064884083 / 5000000000000 : ℝ)
    hlog_90 (by norm_num [quadLogLo, quadLogHi])

private lemma hlog_92 : (3435897043897 / 10000000000000 : ℝ) ≤ Real.log (141 / 100 : ℝ) ∧ Real.log (141 / 100 : ℝ) ≤ (53685891311 / 156250000000 : ℝ) :=
  log_rat_bounds (141 / 100 : ℝ) (1 / 751 : ℝ) (-5) (2) (1) (3435897043897 / 10000000000000 : ℝ) (53685891311 / 156250000000 : ℝ)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hqsub_93 :
    IntervalIntegrable (fun t => Real.log ((7 / 2 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t)) volume (99 / 50 : ℝ) (11 / 5 : ℝ) ∧
      (362381137003 / 10000000000000 : ℝ) ≤ ∫ t in (99 / 50 : ℝ)..(11 / 5 : ℝ), Real.log ((7 / 2 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (99 / 50 : ℝ)..(11 / 5 : ℝ), Real.log ((7 / 2 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ≤ (22648835971 / 625000000000 : ℝ) :=
  quad_log_div_sub (7 / 2 : ℝ) (-1 : ℝ) (0 : ℝ) (1 : ℝ) (99 / 50 : ℝ) (11 / 5 : ℝ) (209 / 100 : ℝ) (11 / 100 : ℝ)
    (141 / 100 : ℝ) (209 / 100 : ℝ) (-100 / 141 : ℝ) (100 / 209 : ℝ) (100 / 141 : ℝ) (3435897043897 / 10000000000000 : ℝ) (53685891311 / 156250000000 : ℝ) (362381137003 / 10000000000000 : ℝ) (22648835971 / 625000000000 : ℝ)
    hlog_92 (by norm_num [quadLogLo, quadLogHi])

private lemma hqchain_94 :
    IntervalIntegrable (fun t => Real.log ((7 / 2 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t)) volume (71 / 46 : ℝ) (99 / 50 : ℝ) ∧
      (276682526959 / 2000000000000 : ℝ) ≤ ∫ t in (71 / 46 : ℝ)..(99 / 50 : ℝ), Real.log ((7 / 2 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (71 / 46 : ℝ)..(99 / 50 : ℝ), Real.log ((7 / 2 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ≤ (1383412863767 / 10000000000000 : ℝ) :=
  chain_int_bounds hqsub_89 hqsub_91 (by norm_num)

private lemma hqchain_95 :
    IntervalIntegrable (fun t => Real.log ((7 / 2 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t)) volume (71 / 46 : ℝ) (11 / 5 : ℝ) ∧
      (872896885899 / 5000000000000 : ℝ) ≤ ∫ t in (71 / 46 : ℝ)..(11 / 5 : ℝ), Real.log ((7 / 2 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (71 / 46 : ℝ)..(11 / 5 : ℝ), Real.log ((7 / 2 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ≤ (1745794239303 / 10000000000000 : ℝ) :=
  chain_int_bounds hqchain_94 hqsub_93 (by norm_num)

private lemma hact_tl_96 :
    IntervalIntegrable (fun t => Real.log ((t + 1) / ((13 / 10 : ℝ) * ((7 / 2 : ℝ) - t))) / ((5 : ℝ) * t)) volume (71 / 46 : ℝ) (11 / 5 : ℝ) ∧
      (5157039891 / 250000000000 : ℝ) ≤ ∫ t in (71 / 46 : ℝ)..(11 / 5 : ℝ), Real.log ((t + 1) / ((13 / 10 : ℝ) * ((7 / 2 : ℝ) - t))) / ((5 : ℝ) * t) :=
  active_t_lin (5 : ℝ) (13 / 10 : ℝ) (7 / 2 : ℝ) (71 / 46 : ℝ) (11 / 5 : ℝ) (506 / 355 : ℝ) (262364264467 / 1000000000000 : ℝ) (65591066117 / 250000000000 : ℝ) (886047199529 / 2500000000000 : ℝ) (886047199531 / 2500000000000 : ℝ)
    (3707070704659 / 10000000000000 : ℝ) (1853535453981 / 5000000000000 : ℝ) (872896885899 / 5000000000000 : ℝ) (1745794239303 / 10000000000000 : ℝ) (5157039891 / 250000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog_78 hlog_79 hqchain_87 hqchain_95 (by norm_num)

private lemma hterm_77 :
    IntervalIntegrable (fun t => ind (71 / 46 : ℝ) (5 / 2 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) / ((13 / 10 : ℝ) * ((7 / 2 : ℝ) - t)))) volume (1 : ℝ) (11 / 5 : ℝ) ∧
      (5157039891 / 250000000000 : ℝ) ≤ ∫ t in (1 : ℝ)..(11 / 5 : ℝ), ind (71 / 46 : ℝ) (5 / 2 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) / ((13 / 10 : ℝ) * ((7 / 2 : ℝ) - t))) :=
  bound_ind_div_active (1 : ℝ) (11 / 5 : ℝ) (71 / 46 : ℝ) (5 / 2 : ℝ) (71 / 46 : ℝ) (11 / 5 : ℝ) (5157039891 / 250000000000 : ℝ)
    (fun t => (5 : ℝ) * t) (fun t => (t + 1) / ((13 / 10 : ℝ) * ((7 / 2 : ℝ) - t)))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (Or.inr rfl) (Or.inl rfl) hact_tl_96

private lemma hlog_98 : (7817179289359 / 5000000000000 : ℝ) ≤ Real.log (5969 / 1250 : ℝ) ∧ Real.log (5969 / 1250 : ℝ) ≤ (7817179289363 / 5000000000000 : ℝ) :=
  log_rat_bounds (5969 / 1250 : ℝ) (1163 / 321163 : ℝ) (7) (-3) (0) (7817179289359 / 5000000000000 : ℝ) (7817179289363 / 5000000000000 : ℝ)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hlog_99 : (3566749439383 / 10000000000000 : ℝ) ≤ Real.log (10 / 7 : ℝ) ∧ Real.log (10 / 7 : ℝ) ≤ (3566749439391 / 10000000000000 : ℝ) :=
  log_rat_bounds (10 / 7 : ℝ) (1 / 449 : ℝ) (6) (-2) (-1) (3566749439383 / 10000000000000 : ℝ) (3566749439391 / 10000000000000 : ℝ)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hlog_100 : (9745596399977 / 10000000000000 : ℝ) ≤ Real.log (53 / 20 : ℝ) ∧ Real.log (53 / 20 : ℝ) ≤ (1949119279997 / 2000000000000 : ℝ) :=
  log_rat_bounds (53 / 20 : ℝ) (11 / 1261 : ℝ) (-4) (-1) (3) (9745596399977 / 10000000000000 : ℝ) (1949119279997 / 2000000000000 : ℝ)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hqsub_101 :
    IntervalIntegrable (fun t => Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t)) volume (77 / 50 : ℝ) (44 / 25 : ℝ) ∧
      (1299725256391 / 10000000000000 : ℝ) ≤ ∫ t in (77 / 50 : ℝ)..(44 / 25 : ℝ), Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (77 / 50 : ℝ)..(44 / 25 : ℝ), Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ≤ (324931347889 / 2500000000000 : ℝ) :=
  quad_log_div_sub (1 : ℝ) (1 : ℝ) (0 : ℝ) (1 : ℝ) (77 / 50 : ℝ) (44 / 25 : ℝ) (33 / 20 : ℝ) (11 / 100 : ℝ)
    (53 / 20 : ℝ) (33 / 20 : ℝ) (20 / 53 : ℝ) (20 / 33 : ℝ) (20 / 33 : ℝ) (9745596399977 / 10000000000000 : ℝ) (1949119279997 / 2000000000000 : ℝ) (1299725256391 / 10000000000000 : ℝ) (324931347889 / 2500000000000 : ℝ)
    hlog_100 (by norm_num [quadLogLo, quadLogHi])

private lemma hqsub_102 :
    IntervalIntegrable (fun t => Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t)) volume (44 / 25 : ℝ) (99 / 50 : ℝ) ∧
      (1240625681543 / 10000000000000 : ℝ) ≤ ∫ t in (44 / 25 : ℝ)..(99 / 50 : ℝ), Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (44 / 25 : ℝ)..(99 / 50 : ℝ), Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ≤ (620312869221 / 5000000000000 : ℝ) :=
  quad_log_div_sub (1 : ℝ) (1 : ℝ) (0 : ℝ) (1 : ℝ) (44 / 25 : ℝ) (99 / 50 : ℝ) (187 / 100 : ℝ) (11 / 100 : ℝ)
    (287 / 100 : ℝ) (187 / 100 : ℝ) (100 / 287 : ℝ) (100 / 187 : ℝ) (100 / 187 : ℝ) (1054312029771 / 1000000000000 : ℝ) (10543120297719 / 10000000000000 : ℝ) (1240625681543 / 10000000000000 : ℝ) (620312869221 / 5000000000000 : ℝ)
    hlog_82 (by norm_num [quadLogLo, quadLogHi])

private lemma hqsub_103 :
    IntervalIntegrable (fun t => Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t)) volume (99 / 50 : ℝ) (11 / 5 : ℝ) ∧
      (148470676741 / 1250000000000 : ℝ) ≤ ∫ t in (99 / 50 : ℝ)..(11 / 5 : ℝ), Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (99 / 50 : ℝ)..(11 / 5 : ℝ), Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ≤ (148470680039 / 1250000000000 : ℝ) :=
  quad_log_div_sub (1 : ℝ) (1 : ℝ) (0 : ℝ) (1 : ℝ) (99 / 50 : ℝ) (11 / 5 : ℝ) (209 / 100 : ℝ) (11 / 100 : ℝ)
    (309 / 100 : ℝ) (209 / 100 : ℝ) (100 / 309 : ℝ) (100 / 209 : ℝ) (100 / 209 : ℝ) (11281710909091 / 10000000000000 : ℝ) (11281710909101 / 10000000000000 : ℝ) (148470676741 / 1250000000000 : ℝ) (148470680039 / 1250000000000 : ℝ)
    hlog_84 (by norm_num [quadLogLo, quadLogHi])

private lemma hqchain_104 :
    IntervalIntegrable (fun t => Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t)) volume (77 / 50 : ℝ) (99 / 50 : ℝ) ∧
      (1270175468967 / 5000000000000 : ℝ) ≤ ∫ t in (77 / 50 : ℝ)..(99 / 50 : ℝ), Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (77 / 50 : ℝ)..(99 / 50 : ℝ), Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ≤ (1270175564999 / 5000000000000 : ℝ) :=
  chain_int_bounds hqsub_101 hqsub_102 (by norm_num)

private lemma hqchain_105 :
    IntervalIntegrable (fun t => Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t)) volume (77 / 50 : ℝ) (11 / 5 : ℝ) ∧
      (1864058175931 / 5000000000000 : ℝ) ≤ ∫ t in (77 / 50 : ℝ)..(11 / 5 : ℝ), Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (77 / 50 : ℝ)..(11 / 5 : ℝ), Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ≤ (372811657031 / 1000000000000 : ℝ) :=
  chain_int_bounds hqchain_104 hqsub_103 (by norm_num)

private lemma hact_tp_106 :
    IntervalIntegrable (fun t => Real.log ((t + 1) ^ (2 : ℕ) / (5969 / 1250 : ℝ)) / ((5 : ℝ) * t)) volume (77 / 50 : ℝ) (11 / 5 : ℝ) ∧
      (187984873413 / 5000000000000 : ℝ) ≤ ∫ t in (77 / 50 : ℝ)..(11 / 5 : ℝ), Real.log ((t + 1) ^ (2 : ℕ) / (5969 / 1250 : ℝ)) / ((5 : ℝ) * t) :=
  active_t_pow 2 (5 : ℝ) (5969 / 1250 : ℝ) (77 / 50 : ℝ) (11 / 5 : ℝ) (10 / 7 : ℝ) (7817179289359 / 5000000000000 : ℝ) (7817179289363 / 5000000000000 : ℝ) (3566749439383 / 10000000000000 : ℝ) (3566749439391 / 10000000000000 : ℝ)
    (1864058175931 / 5000000000000 : ℝ) (372811657031 / 1000000000000 : ℝ) (187984873413 / 5000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hlog_98 hlog_99 hqchain_105 (by norm_num)

private lemma hterm_97 :
    IntervalIntegrable (fun t => ind (77 / 50 : ℝ) (5 / 2 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) ^ (2 : ℕ) / (5969 / 1250 : ℝ))) volume (1 : ℝ) (11 / 5 : ℝ) ∧
      (187984873413 / 5000000000000 : ℝ) ≤ ∫ t in (1 : ℝ)..(11 / 5 : ℝ), ind (77 / 50 : ℝ) (5 / 2 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) ^ (2 : ℕ) / (5969 / 1250 : ℝ)) :=
  bound_ind_div_active (1 : ℝ) (11 / 5 : ℝ) (77 / 50 : ℝ) (5 / 2 : ℝ) (77 / 50 : ℝ) (11 / 5 : ℝ) (187984873413 / 5000000000000 : ℝ)
    (fun t => (5 : ℝ) * t) (fun t => (t + 1) ^ (2 : ℕ) / (5969 / 1250 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (Or.inr rfl) (Or.inl rfl) hact_tp_106

private lemma hlog_108 : (188009674597 / 125000000000 : ℝ) ≤ Real.log (9 / 2 : ℝ) ∧ Real.log (9 / 2 : ℝ) ≤ (3760193491941 / 2500000000000 : ℝ) :=
  log_rat_bounds (9 / 2 : ℝ) (0 : ℝ) (-1) (2) (0) (188009674597 / 125000000000 : ℝ) (3760193491941 / 2500000000000 : ℝ)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hlog_109 : (1797729124713 / 10000000000000 : ℝ) ≤ Real.log (5251 / 4387 : ℝ) ∧ Real.log (5251 / 4387 : ℝ) ≤ (22471614059 / 125000000000 : ℝ) :=
  log_rat_bounds (5251 / 4387 : ℝ) (1393 / 282161 : ℝ) (5) (-3) (0) (1797729124713 / 10000000000000 : ℝ) (22471614059 / 125000000000 : ℝ)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hlog_110 : (908377838329 / 10000000000000 : ℝ) ≤ Real.log (4975 / 4543 : ℝ) ∧ Real.log (4975 / 4543 : ℝ) ≤ (3548350931 / 39062500000 : ℝ) :=
  log_rat_bounds (4975 / 4543 : ℝ) (857 / 123518 : ℝ) (0) (3) (-2) (908377838329 / 10000000000000 : ℝ) (3548350931 / 39062500000 : ℝ)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hlog_111 : (2302912792669 / 1250000000000 : ℝ) ≤ Real.log (1136021 / 180000 : ℝ) ∧ Real.log (1136021 / 180000 : ℝ) ≤ (18423302341357 / 10000000000000 : ℝ) :=
  log_rat_bounds (1136021 / 180000 : ℝ) (11021 / 2261021 : ℝ) (-2) (0) (2) (2302912792669 / 1250000000000 : ℝ) (18423302341357 / 10000000000000 : ℝ)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hqsub_112 :
    IntervalIntegrable (fun t => Real.log ((1143 / 100 : ℝ) + (-177 / 50 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t)) volume (4387 / 3186 : ℝ) (303 / 200 : ℝ) ∧
      (176043922401 / 1000000000000 : ℝ) ≤ ∫ t in (4387 / 3186 : ℝ)..(303 / 200 : ℝ), Real.log ((1143 / 100 : ℝ) + (-177 / 50 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (4387 / 3186 : ℝ)..(303 / 200 : ℝ), Real.log ((1143 / 100 : ℝ) + (-177 / 50 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ≤ (880219619301 / 5000000000000 : ℝ) :=
  quad_log_div_sub (1143 / 100 : ℝ) (-177 / 50 : ℝ) (0 : ℝ) (1 : ℝ) (4387 / 3186 : ℝ) (303 / 200 : ℝ) (921379 / 637200 : ℝ) (43979 / 637200 : ℝ)
    (1136021 / 180000 : ℝ) (921379 / 637200 : ℝ) (-637200 / 1136021 : ℝ) (637200 / 921379 : ℝ) (637200 / 921379 : ℝ) (2302912792669 / 1250000000000 : ℝ) (18423302341357 / 10000000000000 : ℝ) (176043922401 / 1000000000000 : ℝ) (880219619301 / 5000000000000 : ℝ)
    hlog_111 (by norm_num [quadLogLo, quadLogHi])

private lemma hlog_113 : (17632275747209 / 10000000000000 : ℝ) ≤ Real.log (1049621 / 180000 : ℝ) ∧ Real.log (1049621 / 180000 : ℝ) ≤ (17632275747217 / 10000000000000 : ℝ) :=
  log_rat_bounds (1049621 / 180000 : ℝ) (12821 / 2086421 : ℝ) (4) (2) (-2) (17632275747209 / 10000000000000 : ℝ) (17632275747217 / 10000000000000 : ℝ)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hqsub_114 :
    IntervalIntegrable (fun t => Real.log ((1143 / 100 : ℝ) + (-177 / 50 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t)) volume (303 / 200 : ℝ) (89 / 54 : ℝ) ∧
      (1485536493327 / 10000000000000 : ℝ) ≤ ∫ t in (303 / 200 : ℝ)..(89 / 54 : ℝ), Real.log ((1143 / 100 : ℝ) + (-177 / 50 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (303 / 200 : ℝ)..(89 / 54 : ℝ), Real.log ((1143 / 100 : ℝ) + (-177 / 50 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ≤ (742768249661 / 5000000000000 : ℝ) :=
  quad_log_div_sub (1143 / 100 : ℝ) (-177 / 50 : ℝ) (0 : ℝ) (1 : ℝ) (303 / 200 : ℝ) (89 / 54 : ℝ) (17081 / 10800 : ℝ) (719 / 10800 : ℝ)
    (1049621 / 180000 : ℝ) (17081 / 10800 : ℝ) (-637200 / 1049621 : ℝ) (10800 / 17081 : ℝ) (10800 / 17081 : ℝ) (17632275747209 / 10000000000000 : ℝ) (17632275747217 / 10000000000000 : ℝ) (1485536493327 / 10000000000000 : ℝ) (742768249661 / 5000000000000 : ℝ)
    hlog_113 (by norm_num [quadLogLo, quadLogHi])

private lemma hqchain_115 :
    IntervalIntegrable (fun t => Real.log ((1143 / 100 : ℝ) + (-177 / 50 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t)) volume (4387 / 3186 : ℝ) (89 / 54 : ℝ) ∧
      (3245975717337 / 10000000000000 : ℝ) ≤ ∫ t in (4387 / 3186 : ℝ)..(89 / 54 : ℝ), Real.log ((1143 / 100 : ℝ) + (-177 / 50 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (4387 / 3186 : ℝ)..(89 / 54 : ℝ), Real.log ((1143 / 100 : ℝ) + (-177 / 50 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ≤ (811493934481 / 2500000000000 : ℝ) :=
  chain_int_bounds hqsub_112 hqsub_114 (by norm_num)

private lemma hlog_116 : (18042734345193 / 10000000000000 : ℝ) ≤ Real.log (1367 / 225 : ℝ) ∧ Real.log (1367 / 225 : ℝ) ≤ (4510683586299 / 2500000000000 : ℝ) :=
  log_rat_bounds (1367 / 225 : ℝ) (17 / 2717 : ℝ) (1) (1) (0) (18042734345193 / 10000000000000 : ℝ) (4510683586299 / 2500000000000 : ℝ)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hqsub_117 :
    IntervalIntegrable (fun t => Real.log ((1143 / 100 : ℝ) + (-177 / 50 : ℝ) * t) / ((9 / 2 : ℝ) + (-1 : ℝ) * t)) volume (4387 / 3186 : ℝ) (89 / 54 : ℝ) ∧
      (1636926895219 / 10000000000000 : ℝ) ≤ ∫ t in (4387 / 3186 : ℝ)..(89 / 54 : ℝ), Real.log ((1143 / 100 : ℝ) + (-177 / 50 : ℝ) * t) / ((9 / 2 : ℝ) + (-1 : ℝ) * t) ∧
      ∫ t in (4387 / 3186 : ℝ)..(89 / 54 : ℝ), Real.log ((1143 / 100 : ℝ) + (-177 / 50 : ℝ) * t) / ((9 / 2 : ℝ) + (-1 : ℝ) * t) ≤ (1636927118243 / 10000000000000 : ℝ) :=
  quad_log_div_sub (1143 / 100 : ℝ) (-177 / 50 : ℝ) (9 / 2 : ℝ) (-1 : ℝ) (4387 / 3186 : ℝ) (89 / 54 : ℝ) (4819 / 3186 : ℝ) (8 / 59 : ℝ)
    (1367 / 225 : ℝ) (4759 / 1593 : ℝ) (-1593 / 2734 : ℝ) (-1593 / 4759 : ℝ) (1593 / 2734 : ℝ) (18042734345193 / 10000000000000 : ℝ) (4510683586299 / 2500000000000 : ℝ) (1636926895219 / 10000000000000 : ℝ) (1636927118243 / 10000000000000 : ℝ)
    hlog_116 (by norm_num [quadLogLo, quadLogHi])

private lemma hlog_118 : (2144034527649 / 2000000000000 : ℝ) ≤ Real.log (6894189 / 2360000 : ℝ) ∧ Real.log (6894189 / 2360000 : ℝ) ≤ (10720172638253 / 10000000000000 : ℝ) :=
  log_rat_bounds (6894189 / 2360000 : ℝ) (10821 / 1521221 : ℝ) (3) (2) (-2) (2144034527649 / 2000000000000 : ℝ) (10720172638253 / 10000000000000 : ℝ)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hqsub_119 :
    IntervalIntegrable (fun t => Real.log ((1287 / 200 : ℝ) + (-243 / 100 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t)) volume (4387 / 3186 : ℝ) (303 / 200 : ℝ) ∧
      (128063851461 / 1250000000000 : ℝ) ≤ ∫ t in (4387 / 3186 : ℝ)..(303 / 200 : ℝ), Real.log ((1287 / 200 : ℝ) + (-243 / 100 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (4387 / 3186 : ℝ)..(303 / 200 : ℝ), Real.log ((1287 / 200 : ℝ) + (-243 / 100 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ≤ (1024510847799 / 10000000000000 : ℝ) :=
  quad_log_div_sub (1287 / 200 : ℝ) (-243 / 100 : ℝ) (0 : ℝ) (1 : ℝ) (4387 / 3186 : ℝ) (303 / 200 : ℝ) (921379 / 637200 : ℝ) (43979 / 637200 : ℝ)
    (6894189 / 2360000 : ℝ) (921379 / 637200 : ℝ) (-637200 / 766021 : ℝ) (637200 / 921379 : ℝ) (637200 / 766021 : ℝ) (2144034527649 / 2000000000000 : ℝ) (10720172638253 / 10000000000000 : ℝ) (128063851461 / 1250000000000 : ℝ) (1024510847799 / 10000000000000 : ℝ)
    hlog_118 (by norm_num [quadLogLo, quadLogHi])

private lemma hlog_120 : (4761714845831 / 5000000000000 : ℝ) ≤ Real.log (103671 / 40000 : ℝ) ∧ Real.log (103671 / 40000 : ℝ) ≤ (952342969167 / 1000000000000 : ℝ) :=
  log_rat_bounds (103671 / 40000 : ℝ) (1271 / 206071 : ℝ) (6) (0) (-2) (4761714845831 / 5000000000000 : ℝ) (952342969167 / 1000000000000 : ℝ)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hqsub_121 :
    IntervalIntegrable (fun t => Real.log ((1287 / 200 : ℝ) + (-243 / 100 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t)) volume (303 / 200 : ℝ) (89 / 54 : ℝ) ∧
      (802414806937 / 10000000000000 : ℝ) ≤ ∫ t in (303 / 200 : ℝ)..(89 / 54 : ℝ), Real.log ((1287 / 200 : ℝ) + (-243 / 100 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (303 / 200 : ℝ)..(89 / 54 : ℝ), Real.log ((1287 / 200 : ℝ) + (-243 / 100 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ≤ (160482971487 / 2000000000000 : ℝ) :=
  quad_log_div_sub (1287 / 200 : ℝ) (-243 / 100 : ℝ) (0 : ℝ) (1 : ℝ) (303 / 200 : ℝ) (89 / 54 : ℝ) (17081 / 10800 : ℝ) (719 / 10800 : ℝ)
    (103671 / 40000 : ℝ) (17081 / 10800 : ℝ) (-10800 / 11519 : ℝ) (10800 / 17081 : ℝ) (10800 / 11519 : ℝ) (4761714845831 / 5000000000000 : ℝ) (952342969167 / 1000000000000 : ℝ) (802414806937 / 10000000000000 : ℝ) (160482971487 / 2000000000000 : ℝ)
    hlog_120 (by norm_num [quadLogLo, quadLogHi])

private lemma hqchain_122 :
    IntervalIntegrable (fun t => Real.log ((1287 / 200 : ℝ) + (-243 / 100 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t)) volume (4387 / 3186 : ℝ) (89 / 54 : ℝ) ∧
      (14615404949 / 80000000000 : ℝ) ≤ ∫ t in (4387 / 3186 : ℝ)..(89 / 54 : ℝ), Real.log ((1287 / 200 : ℝ) + (-243 / 100 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (4387 / 3186 : ℝ)..(89 / 54 : ℝ), Real.log ((1287 / 200 : ℝ) + (-243 / 100 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ≤ (913462852617 / 5000000000000 : ℝ) :=
  chain_int_bounds hqsub_119 hqsub_121 (by norm_num)

private lemma hqsub_123 :
    IntervalIntegrable (fun t => Real.log ((1287 / 200 : ℝ) + (-243 / 100 : ℝ) * t) / ((9 / 2 : ℝ) + (-1 : ℝ) * t)) volume (4387 / 3186 : ℝ) (303 / 200 : ℝ) ∧
      (121044543203 / 2500000000000 : ℝ) ≤ ∫ t in (4387 / 3186 : ℝ)..(303 / 200 : ℝ), Real.log ((1287 / 200 : ℝ) + (-243 / 100 : ℝ) * t) / ((9 / 2 : ℝ) + (-1 : ℝ) * t) ∧
      ∫ t in (4387 / 3186 : ℝ)..(303 / 200 : ℝ), Real.log ((1287 / 200 : ℝ) + (-243 / 100 : ℝ) * t) / ((9 / 2 : ℝ) + (-1 : ℝ) * t) ≤ (484178189011 / 10000000000000 : ℝ) :=
  quad_log_div_sub (1287 / 200 : ℝ) (-243 / 100 : ℝ) (9 / 2 : ℝ) (-1 : ℝ) (4387 / 3186 : ℝ) (303 / 200 : ℝ) (921379 / 637200 : ℝ) (43979 / 637200 : ℝ)
    (6894189 / 2360000 : ℝ) (1946021 / 637200 : ℝ) (-637200 / 766021 : ℝ) (-637200 / 1946021 : ℝ) (637200 / 766021 : ℝ) (2144034527649 / 2000000000000 : ℝ) (10720172638253 / 10000000000000 : ℝ) (121044543203 / 2500000000000 : ℝ) (484178189011 / 10000000000000 : ℝ)
    hlog_118 (by norm_num [quadLogLo, quadLogHi])

private lemma hqsub_124 :
    IntervalIntegrable (fun t => Real.log ((1287 / 200 : ℝ) + (-243 / 100 : ℝ) * t) / ((9 / 2 : ℝ) + (-1 : ℝ) * t)) volume (303 / 200 : ℝ) (89 / 54 : ℝ) ∧
      (217025979151 / 5000000000000 : ℝ) ≤ ∫ t in (303 / 200 : ℝ)..(89 / 54 : ℝ), Real.log ((1287 / 200 : ℝ) + (-243 / 100 : ℝ) * t) / ((9 / 2 : ℝ) + (-1 : ℝ) * t) ∧
      ∫ t in (303 / 200 : ℝ)..(89 / 54 : ℝ), Real.log ((1287 / 200 : ℝ) + (-243 / 100 : ℝ) * t) / ((9 / 2 : ℝ) + (-1 : ℝ) * t) ≤ (86810397059 / 2000000000000 : ℝ) :=
  quad_log_div_sub (1287 / 200 : ℝ) (-243 / 100 : ℝ) (9 / 2 : ℝ) (-1 : ℝ) (303 / 200 : ℝ) (89 / 54 : ℝ) (17081 / 10800 : ℝ) (719 / 10800 : ℝ)
    (103671 / 40000 : ℝ) (31519 / 10800 : ℝ) (-10800 / 11519 : ℝ) (-10800 / 31519 : ℝ) (10800 / 11519 : ℝ) (4761714845831 / 5000000000000 : ℝ) (952342969167 / 1000000000000 : ℝ) (217025979151 / 5000000000000 : ℝ) (86810397059 / 2000000000000 : ℝ)
    hlog_120 (by norm_num [quadLogLo, quadLogHi])

private lemma hqchain_125 :
    IntervalIntegrable (fun t => Real.log ((1287 / 200 : ℝ) + (-243 / 100 : ℝ) * t) / ((9 / 2 : ℝ) + (-1 : ℝ) * t)) volume (4387 / 3186 : ℝ) (89 / 54 : ℝ) ∧
      (459115065557 / 5000000000000 : ℝ) ≤ ∫ t in (4387 / 3186 : ℝ)..(89 / 54 : ℝ), Real.log ((1287 / 200 : ℝ) + (-243 / 100 : ℝ) * t) / ((9 / 2 : ℝ) + (-1 : ℝ) * t) ∧
      ∫ t in (4387 / 3186 : ℝ)..(89 / 54 : ℝ), Real.log ((1287 / 200 : ℝ) + (-243 / 100 : ℝ) * t) / ((9 / 2 : ℝ) + (-1 : ℝ) * t) ≤ (459115087153 / 5000000000000 : ℝ) :=
  chain_int_bounds hqsub_123 hqsub_124 (by norm_num)

private lemma hact_q6_126 :
    IntervalIntegrable (fun t => Real.log ((9 / 2 : ℝ) ^ (2 : ℕ) / (((177 / 50 : ℝ) * (9 / 2 : ℝ) - (9 / 2 : ℝ) - (177 / 50 : ℝ) * t) * ((243 / 100 : ℝ) * (9 / 2 : ℝ) - (9 / 2 : ℝ) - (243 / 100 : ℝ) * t))) / (5 * t * (1 - t / (9 / 2 : ℝ)))) volume (4387 / 3186 : ℝ) (89 / 54 : ℝ) ∧
      (51232989703 / 5000000000000 : ℝ) ≤ ∫ t in (4387 / 3186 : ℝ)..(89 / 54 : ℝ), Real.log ((9 / 2 : ℝ) ^ (2 : ℕ) / (((177 / 50 : ℝ) * (9 / 2 : ℝ) - (9 / 2 : ℝ) - (177 / 50 : ℝ) * t) * ((243 / 100 : ℝ) * (9 / 2 : ℝ) - (9 / 2 : ℝ) - (243 / 100 : ℝ) * t))) / (5 * t * (1 - t / (9 / 2 : ℝ))) :=
  active_q_6 (9 / 2 : ℝ) (177 / 50 : ℝ) (243 / 100 : ℝ) (1143 / 100 : ℝ) (-177 / 50 : ℝ) (1287 / 200 : ℝ) (-243 / 100 : ℝ) (4387 / 3186 : ℝ) (89 / 54 : ℝ) (5251 / 4387 : ℝ) (4975 / 4543 : ℝ)
    (188009674597 / 125000000000 : ℝ) (3760193491941 / 2500000000000 : ℝ) (1797729124713 / 10000000000000 : ℝ) (22471614059 / 125000000000 : ℝ) (908377838329 / 10000000000000 : ℝ) (3548350931 / 39062500000 : ℝ)
    (3245975717337 / 10000000000000 : ℝ) (811493934481 / 2500000000000 : ℝ) (1636926895219 / 10000000000000 : ℝ) (1636927118243 / 10000000000000 : ℝ) (14615404949 / 80000000000 : ℝ) (913462852617 / 5000000000000 : ℝ) (459115065557 / 5000000000000 : ℝ) (459115087153 / 5000000000000 : ℝ) (51232989703 / 5000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog_108 hlog_109 hlog_110 hqchain_115 hqsub_117 hqchain_122 hqchain_125 (by norm_num)

private lemma hterm_107 :
    IntervalIntegrable (fun t => ind (4387 / 3186 : ℝ) (89 / 54 : ℝ) t / (5 * t * (1 - t / (9 / 2 : ℝ))) * Real.log ((9 / 2 : ℝ) ^ (2 : ℕ) / (((177 / 50 : ℝ) * (9 / 2 : ℝ) - (9 / 2 : ℝ) - (177 / 50 : ℝ) * t) * ((243 / 100 : ℝ) * (9 / 2 : ℝ) - (9 / 2 : ℝ) - (243 / 100 : ℝ) * t)))) volume (1 : ℝ) (11 / 5 : ℝ) ∧
      (51232989703 / 5000000000000 : ℝ) ≤ ∫ t in (1 : ℝ)..(11 / 5 : ℝ), ind (4387 / 3186 : ℝ) (89 / 54 : ℝ) t / (5 * t * (1 - t / (9 / 2 : ℝ))) * Real.log ((9 / 2 : ℝ) ^ (2 : ℕ) / (((177 / 50 : ℝ) * (9 / 2 : ℝ) - (9 / 2 : ℝ) - (177 / 50 : ℝ) * t) * ((243 / 100 : ℝ) * (9 / 2 : ℝ) - (9 / 2 : ℝ) - (243 / 100 : ℝ) * t))) :=
  bound_ind_div_active (1 : ℝ) (11 / 5 : ℝ) (4387 / 3186 : ℝ) (89 / 54 : ℝ) (4387 / 3186 : ℝ) (89 / 54 : ℝ) (51232989703 / 5000000000000 : ℝ)
    (fun t => 5 * t * (1 - t / (9 / 2 : ℝ))) (fun t => (9 / 2 : ℝ) ^ (2 : ℕ) / (((177 / 50 : ℝ) * (9 / 2 : ℝ) - (9 / 2 : ℝ) - (177 / 50 : ℝ) * t) * ((243 / 100 : ℝ) * (9 / 2 : ℝ) - (9 / 2 : ℝ) - (243 / 100 : ℝ) * t)))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (Or.inr rfl) (Or.inr rfl) hact_q6_126

private lemma hlog_128 : (109614137449 / 10000000000000 : ℝ) ≤ Real.log (42471 / 42008 : ℝ) ∧ Real.log (42471 / 42008 : ℝ) ≤ (2192282749 / 200000000000 : ℝ) :=
  log_rat_bounds (42471 / 42008 : ℝ) (463 / 84479 : ℝ) (0) (0) (0) (109614137449 / 10000000000000 : ℝ) (2192282749 / 200000000000 : ℝ)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hlog_129 : (63900626647 / 10000000000000 : ℝ) ≤ Real.log (72688 / 72225 : ℝ) ∧ Real.log (72688 / 72225 : ℝ) ≤ (7987578331 / 1250000000000 : ℝ) :=
  log_rat_bounds (72688 / 72225 : ℝ) (463 / 144913 : ℝ) (0) (0) (0) (63900626647 / 10000000000000 : ℝ) (7987578331 / 1250000000000 : ℝ)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hlog_130 : (382043381927 / 625000000000 : ℝ) ≤ Real.log (93937 / 50976 : ℝ) ∧ Real.log (93937 / 50976 : ℝ) ≤ (1528173527709 / 2500000000000 : ℝ) :=
  log_rat_bounds (93937 / 50976 : ℝ) (10901 / 928469 : ℝ) (0) (2) (-1) (382043381927 / 625000000000 : ℝ) (1528173527709 / 2500000000000 : ℝ)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hqsub_131 :
    IntervalIntegrable (fun t => Real.log ((7 / 2 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t)) volume (89 / 54 : ℝ) (1573 / 944 : ℝ) ∧
      (16751078111 / 2500000000000 : ℝ) ≤ ∫ t in (89 / 54 : ℝ)..(1573 / 944 : ℝ), Real.log ((7 / 2 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (89 / 54 : ℝ)..(1573 / 944 : ℝ), Real.log ((7 / 2 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ≤ (13400862489 / 2000000000000 : ℝ) :=
  quad_log_div_sub (7 / 2 : ℝ) (-1 : ℝ) (0 : ℝ) (1 : ℝ) (89 / 54 : ℝ) (1573 / 944 : ℝ) (84479 / 50976 : ℝ) (463 / 50976 : ℝ)
    (93937 / 50976 : ℝ) (84479 / 50976 : ℝ) (-50976 / 93937 : ℝ) (50976 / 84479 : ℝ) (50976 / 84479 : ℝ) (382043381927 / 625000000000 : ℝ) (1528173527709 / 2500000000000 : ℝ) (16751078111 / 2500000000000 : ℝ) (13400862489 / 2000000000000 : ℝ)
    hlog_130 (by norm_num [quadLogLo, quadLogHi])

private lemma hqsub_132 :
    IntervalIntegrable (fun t => Real.log ((7 / 2 : ℝ) + (-1 : ℝ) * t) / ((9 / 2 : ℝ) + (-1 : ℝ) * t)) volume (89 / 54 : ℝ) (1573 / 944 : ℝ) ∧
      (152577751 / 39062500000 : ℝ) ≤ ∫ t in (89 / 54 : ℝ)..(1573 / 944 : ℝ), Real.log ((7 / 2 : ℝ) + (-1 : ℝ) * t) / ((9 / 2 : ℝ) + (-1 : ℝ) * t) ∧
      ∫ t in (89 / 54 : ℝ)..(1573 / 944 : ℝ), Real.log ((7 / 2 : ℝ) + (-1 : ℝ) * t) / ((9 / 2 : ℝ) + (-1 : ℝ) * t) ≤ (39059904257 / 10000000000000 : ℝ) :=
  quad_log_div_sub (7 / 2 : ℝ) (-1 : ℝ) (9 / 2 : ℝ) (-1 : ℝ) (89 / 54 : ℝ) (1573 / 944 : ℝ) (84479 / 50976 : ℝ) (463 / 50976 : ℝ)
    (93937 / 50976 : ℝ) (144913 / 50976 : ℝ) (-50976 / 93937 : ℝ) (-50976 / 144913 : ℝ) (50976 / 93937 : ℝ) (382043381927 / 625000000000 : ℝ) (1528173527709 / 2500000000000 : ℝ) (152577751 / 39062500000 : ℝ) (39059904257 / 10000000000000 : ℝ)
    hlog_130 (by norm_num [quadLogLo, quadLogHi])

private lemma hlog_133 : (8581049657259 / 5000000000000 : ℝ) ≤ Real.log (80113 / 14400 : ℝ) ∧ Real.log (80113 / 14400 : ℝ) ≤ (4290524828631 / 2500000000000 : ℝ) :=
  log_rat_bounds (80113 / 14400 : ℝ) (113 / 160113 : ℝ) (1) (-2) (2) (8581049657259 / 5000000000000 : ℝ) (4290524828631 / 2500000000000 : ℝ)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hqsub_134 :
    IntervalIntegrable (fun t => Real.log ((1143 / 100 : ℝ) + (-177 / 50 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t)) volume (89 / 54 : ℝ) (1573 / 944 : ℝ) ∧
      (3762428369 / 200000000000 : ℝ) ≤ ∫ t in (89 / 54 : ℝ)..(1573 / 944 : ℝ), Real.log ((1143 / 100 : ℝ) + (-177 / 50 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (89 / 54 : ℝ)..(1573 / 944 : ℝ), Real.log ((1143 / 100 : ℝ) + (-177 / 50 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ≤ (188121418451 / 10000000000000 : ℝ) :=
  quad_log_div_sub (1143 / 100 : ℝ) (-177 / 50 : ℝ) (0 : ℝ) (1 : ℝ) (89 / 54 : ℝ) (1573 / 944 : ℝ) (84479 / 50976 : ℝ) (463 / 50976 : ℝ)
    (80113 / 14400 : ℝ) (84479 / 50976 : ℝ) (-50976 / 80113 : ℝ) (50976 / 84479 : ℝ) (50976 / 80113 : ℝ) (8581049657259 / 5000000000000 : ℝ) (4290524828631 / 2500000000000 : ℝ) (3762428369 / 200000000000 : ℝ) (188121418451 / 10000000000000 : ℝ)
    hlog_133 (by norm_num [quadLogLo, quadLogHi])

private lemma hqsub_135 :
    IntervalIntegrable (fun t => Real.log ((1143 / 100 : ℝ) + (-177 / 50 : ℝ) * t) / ((9 / 2 : ℝ) + (-1 : ℝ) * t)) volume (89 / 54 : ℝ) (1573 / 944 : ℝ) ∧
      (54833070519 / 5000000000000 : ℝ) ≤ ∫ t in (89 / 54 : ℝ)..(1573 / 944 : ℝ), Real.log ((1143 / 100 : ℝ) + (-177 / 50 : ℝ) * t) / ((9 / 2 : ℝ) + (-1 : ℝ) * t) ∧
      ∫ t in (89 / 54 : ℝ)..(1573 / 944 : ℝ), Real.log ((1143 / 100 : ℝ) + (-177 / 50 : ℝ) * t) / ((9 / 2 : ℝ) + (-1 : ℝ) * t) ≤ (109666141039 / 10000000000000 : ℝ) :=
  quad_log_div_sub (1143 / 100 : ℝ) (-177 / 50 : ℝ) (9 / 2 : ℝ) (-1 : ℝ) (89 / 54 : ℝ) (1573 / 944 : ℝ) (84479 / 50976 : ℝ) (463 / 50976 : ℝ)
    (80113 / 14400 : ℝ) (144913 / 50976 : ℝ) (-50976 / 80113 : ℝ) (-50976 / 144913 : ℝ) (50976 / 80113 : ℝ) (8581049657259 / 5000000000000 : ℝ) (4290524828631 / 2500000000000 : ℝ) (54833070519 / 5000000000000 : ℝ) (109666141039 / 10000000000000 : ℝ)
    hlog_133 (by norm_num [quadLogLo, quadLogHi])

private lemma hact_q7_136 :
    IntervalIntegrable (fun t => Real.log ((9 / 2 : ℝ) * ((9 / 2 : ℝ) - 1 - t) / ((177 / 50 : ℝ) * (9 / 2 : ℝ) - (9 / 2 : ℝ) - (177 / 50 : ℝ) * t)) / (5 * t * (1 - t / (9 / 2 : ℝ)))) volume (89 / 54 : ℝ) (1573 / 944 : ℝ) ∧
      (6925629189 / 5000000000000 : ℝ) ≤ ∫ t in (89 / 54 : ℝ)..(1573 / 944 : ℝ), Real.log ((9 / 2 : ℝ) * ((9 / 2 : ℝ) - 1 - t) / ((177 / 50 : ℝ) * (9 / 2 : ℝ) - (9 / 2 : ℝ) - (177 / 50 : ℝ) * t)) / (5 * t * (1 - t / (9 / 2 : ℝ))) :=
  active_q_7 (9 / 2 : ℝ) (177 / 50 : ℝ) (7 / 2 : ℝ) (1143 / 100 : ℝ) (-177 / 50 : ℝ) (89 / 54 : ℝ) (1573 / 944 : ℝ) (42471 / 42008 : ℝ) (72688 / 72225 : ℝ)
    (188009674597 / 125000000000 : ℝ) (3760193491941 / 2500000000000 : ℝ) (109614137449 / 10000000000000 : ℝ) (2192282749 / 200000000000 : ℝ) (63900626647 / 10000000000000 : ℝ) (7987578331 / 1250000000000 : ℝ)
    (16751078111 / 2500000000000 : ℝ) (13400862489 / 2000000000000 : ℝ) (152577751 / 39062500000 : ℝ) (39059904257 / 10000000000000 : ℝ) (3762428369 / 200000000000 : ℝ) (188121418451 / 10000000000000 : ℝ) (54833070519 / 5000000000000 : ℝ) (109666141039 / 10000000000000 : ℝ) (6925629189 / 5000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog_108 hlog_128 hlog_129 hqsub_131 hqsub_132 hqsub_134 hqsub_135 (by norm_num)

private lemma hterm_127 :
    IntervalIntegrable (fun t => ind (89 / 54 : ℝ) (1573 / 944 : ℝ) t / (5 * t * (1 - t / (9 / 2 : ℝ))) * Real.log ((9 / 2 : ℝ) * ((9 / 2 : ℝ) - 1 - t) / ((177 / 50 : ℝ) * (9 / 2 : ℝ) - (9 / 2 : ℝ) - (177 / 50 : ℝ) * t))) volume (1 : ℝ) (11 / 5 : ℝ) ∧
      (6925629189 / 5000000000000 : ℝ) ≤ ∫ t in (1 : ℝ)..(11 / 5 : ℝ), ind (89 / 54 : ℝ) (1573 / 944 : ℝ) t / (5 * t * (1 - t / (9 / 2 : ℝ))) * Real.log ((9 / 2 : ℝ) * ((9 / 2 : ℝ) - 1 - t) / ((177 / 50 : ℝ) * (9 / 2 : ℝ) - (9 / 2 : ℝ) - (177 / 50 : ℝ) * t)) :=
  bound_ind_div_active (1 : ℝ) (11 / 5 : ℝ) (89 / 54 : ℝ) (1573 / 944 : ℝ) (89 / 54 : ℝ) (1573 / 944 : ℝ) (6925629189 / 5000000000000 : ℝ)
    (fun t => 5 * t * (1 - t / (9 / 2 : ℝ))) (fun t => (9 / 2 : ℝ) * ((9 / 2 : ℝ) - 1 - t) / ((177 / 50 : ℝ) * (9 / 2 : ℝ) - (9 / 2 : ℝ) - (177 / 50 : ℝ) * t))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (Or.inr rfl) (Or.inr rfl) hact_q7_136

private lemma hlog_138 : (96080002897 / 500000000000 : ℝ) ≤ Real.log (143 / 118 : ℝ) ∧ Real.log (143 / 118 : ℝ) ≤ (240200007243 / 1250000000000 : ℝ) :=
  log_rat_bounds (143 / 118 : ℝ) (7 / 1423 : ℝ) (1) (1) (-1) (96080002897 / 500000000000 : ℝ) (240200007243 / 1250000000000 : ℝ)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hlog_139 : (489278950017 / 5000000000000 : ℝ) ≤ Real.log (118 / 107 : ℝ) ∧ Real.log (118 / 107 : ℝ) ≤ (978557900041 / 10000000000000 : ℝ) :=
  log_rat_bounds (118 / 107 : ℝ) (61 / 5839 : ℝ) (0) (3) (-2) (489278950017 / 5000000000000 : ℝ) (978557900041 / 10000000000000 : ℝ)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hlog_140 : (1820708017631 / 1250000000000 : ℝ) ≤ Real.log (2682 / 625 : ℝ) ∧ Real.log (2682 / 625 : ℝ) ≤ (2913132828211 / 2000000000000 : ℝ) :=
  log_rat_bounds (2682 / 625 : ℝ) (23 / 8023 : ℝ) (6) (-1) (-1) (1820708017631 / 1250000000000 : ℝ) (2913132828211 / 2000000000000 : ℝ)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hqsub_141 :
    IntervalIntegrable (fun t => Real.log ((423 / 50 : ℝ) + (-72 / 25 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t)) volume (11 / 8 : ℝ) (38 / 25 : ℝ) ∧
      (365180807451 / 2500000000000 : ℝ) ≤ ∫ t in (11 / 8 : ℝ)..(38 / 25 : ℝ), Real.log ((423 / 50 : ℝ) + (-72 / 25 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (11 / 8 : ℝ)..(38 / 25 : ℝ), Real.log ((423 / 50 : ℝ) + (-72 / 25 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ≤ (1460723249277 / 10000000000000 : ℝ) :=
  quad_log_div_sub (423 / 50 : ℝ) (-72 / 25 : ℝ) (0 : ℝ) (1 : ℝ) (11 / 8 : ℝ) (38 / 25 : ℝ) (579 / 400 : ℝ) (29 / 400 : ℝ)
    (2682 / 625 : ℝ) (579 / 400 : ℝ) (-100 / 149 : ℝ) (400 / 579 : ℝ) (400 / 579 : ℝ) (1820708017631 / 1250000000000 : ℝ) (2913132828211 / 2000000000000 : ℝ) (365180807451 / 2500000000000 : ℝ) (1460723249277 / 10000000000000 : ℝ)
    hlog_140 (by norm_num [quadLogLo, quadLogHi])

private lemma hlog_142 : (1692119844903 / 1250000000000 : ℝ) ≤ Real.log (571077 / 147500 : ℝ) ∧ Real.log (571077 / 147500 : ℝ) ≤ (211514980613 / 156250000000 : ℝ) :=
  log_rat_bounds (571077 / 147500 : ℝ) (1559 / 379159 : ℝ) (5) (1) (-2) (1692119844903 / 1250000000000 : ℝ) (211514980613 / 156250000000 : ℝ)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hqsub_143 :
    IntervalIntegrable (fun t => Real.log ((423 / 50 : ℝ) + (-72 / 25 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t)) volume (38 / 25 : ℝ) (1573 / 944 : ℝ) ∧
      (311101172291 / 2500000000000 : ℝ) ≤ ∫ t in (38 / 25 : ℝ)..(1573 / 944 : ℝ), Real.log ((423 / 50 : ℝ) + (-72 / 25 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (38 / 25 : ℝ)..(1573 / 944 : ℝ), Real.log ((423 / 50 : ℝ) + (-72 / 25 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ≤ (622202357433 / 5000000000000 : ℝ) :=
  quad_log_div_sub (423 / 50 : ℝ) (-72 / 25 : ℝ) (0 : ℝ) (1 : ℝ) (38 / 25 : ℝ) (1573 / 944 : ℝ) (75197 / 47200 : ℝ) (3453 / 47200 : ℝ)
    (571077 / 147500 : ℝ) (75197 / 47200 : ℝ) (-47200 / 63453 : ℝ) (47200 / 75197 : ℝ) (47200 / 63453 : ℝ) (1692119844903 / 1250000000000 : ℝ) (211514980613 / 156250000000 : ℝ) (311101172291 / 2500000000000 : ℝ) (622202357433 / 5000000000000 : ℝ)
    hlog_142 (by norm_num [quadLogLo, quadLogHi])

private lemma hqchain_144 :
    IntervalIntegrable (fun t => Real.log ((423 / 50 : ℝ) + (-72 / 25 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t)) volume (11 / 8 : ℝ) (1573 / 944 : ℝ) ∧
      (338140989871 / 1250000000000 : ℝ) ≤ ∫ t in (11 / 8 : ℝ)..(1573 / 944 : ℝ), Real.log ((423 / 50 : ℝ) + (-72 / 25 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (11 / 8 : ℝ)..(1573 / 944 : ℝ), Real.log ((423 / 50 : ℝ) + (-72 / 25 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ≤ (2705127964143 / 10000000000000 : ℝ) :=
  chain_int_bounds hqsub_141 hqsub_143 (by norm_num)

private lemma hqsub_145 :
    IntervalIntegrable (fun t => Real.log ((423 / 50 : ℝ) + (-72 / 25 : ℝ) * t) / ((9 / 2 : ℝ) + (-1 : ℝ) * t)) volume (11 / 8 : ℝ) (38 / 25 : ℝ) ∧
      (345829119107 / 5000000000000 : ℝ) ≤ ∫ t in (11 / 8 : ℝ)..(38 / 25 : ℝ), Real.log ((423 / 50 : ℝ) + (-72 / 25 : ℝ) * t) / ((9 / 2 : ℝ) + (-1 : ℝ) * t) ∧
      ∫ t in (11 / 8 : ℝ)..(38 / 25 : ℝ), Real.log ((423 / 50 : ℝ) + (-72 / 25 : ℝ) * t) / ((9 / 2 : ℝ) + (-1 : ℝ) * t) ≤ (691658244539 / 10000000000000 : ℝ) :=
  quad_log_div_sub (423 / 50 : ℝ) (-72 / 25 : ℝ) (9 / 2 : ℝ) (-1 : ℝ) (11 / 8 : ℝ) (38 / 25 : ℝ) (579 / 400 : ℝ) (29 / 400 : ℝ)
    (2682 / 625 : ℝ) (1221 / 400 : ℝ) (-100 / 149 : ℝ) (-400 / 1221 : ℝ) (100 / 149 : ℝ) (1820708017631 / 1250000000000 : ℝ) (2913132828211 / 2000000000000 : ℝ) (345829119107 / 5000000000000 : ℝ) (691658244539 / 10000000000000 : ℝ)
    hlog_140 (by norm_num [quadLogLo, quadLogHi])

private lemma hqsub_146 :
    IntervalIntegrable (fun t => Real.log ((423 / 50 : ℝ) + (-72 / 25 : ℝ) * t) / ((9 / 2 : ℝ) + (-1 : ℝ) * t)) volume (38 / 25 : ℝ) (1573 / 944 : ℝ) ∧
      (681036823867 / 10000000000000 : ℝ) ≤ ∫ t in (38 / 25 : ℝ)..(1573 / 944 : ℝ), Real.log ((423 / 50 : ℝ) + (-72 / 25 : ℝ) * t) / ((9 / 2 : ℝ) + (-1 : ℝ) * t) ∧
      ∫ t in (38 / 25 : ℝ)..(1573 / 944 : ℝ), Real.log ((423 / 50 : ℝ) + (-72 / 25 : ℝ) * t) / ((9 / 2 : ℝ) + (-1 : ℝ) * t) ≤ (681036836967 / 10000000000000 : ℝ) :=
  quad_log_div_sub (423 / 50 : ℝ) (-72 / 25 : ℝ) (9 / 2 : ℝ) (-1 : ℝ) (38 / 25 : ℝ) (1573 / 944 : ℝ) (75197 / 47200 : ℝ) (3453 / 47200 : ℝ)
    (571077 / 147500 : ℝ) (137203 / 47200 : ℝ) (-47200 / 63453 : ℝ) (-47200 / 137203 : ℝ) (47200 / 63453 : ℝ) (1692119844903 / 1250000000000 : ℝ) (211514980613 / 156250000000 : ℝ) (681036823867 / 10000000000000 : ℝ) (681036836967 / 10000000000000 : ℝ)
    hlog_142 (by norm_num [quadLogLo, quadLogHi])

private lemma hqchain_147 :
    IntervalIntegrable (fun t => Real.log ((423 / 50 : ℝ) + (-72 / 25 : ℝ) * t) / ((9 / 2 : ℝ) + (-1 : ℝ) * t)) volume (11 / 8 : ℝ) (1573 / 944 : ℝ) ∧
      (1372695062081 / 10000000000000 : ℝ) ≤ ∫ t in (11 / 8 : ℝ)..(1573 / 944 : ℝ), Real.log ((423 / 50 : ℝ) + (-72 / 25 : ℝ) * t) / ((9 / 2 : ℝ) + (-1 : ℝ) * t) ∧
      ∫ t in (11 / 8 : ℝ)..(1573 / 944 : ℝ), Real.log ((423 / 50 : ℝ) + (-72 / 25 : ℝ) * t) / ((9 / 2 : ℝ) + (-1 : ℝ) * t) ≤ (686347540753 / 5000000000000 : ℝ) :=
  chain_int_bounds hqsub_145 hqsub_146 (by norm_num)

private lemma hact_q8_148 :
    IntervalIntegrable (fun t => Real.log ((9 / 2 : ℝ) / ((72 / 25 : ℝ) * (9 / 2 : ℝ) - (9 / 2 : ℝ) - (72 / 25 : ℝ) * t)) / (5 * t * (1 - t / (9 / 2 : ℝ)))) volume (11 / 8 : ℝ) (1573 / 944 : ℝ) ∧
      (56847797203 / 10000000000000 : ℝ) ≤ ∫ t in (11 / 8 : ℝ)..(1573 / 944 : ℝ), Real.log ((9 / 2 : ℝ) / ((72 / 25 : ℝ) * (9 / 2 : ℝ) - (9 / 2 : ℝ) - (72 / 25 : ℝ) * t)) / (5 * t * (1 - t / (9 / 2 : ℝ))) :=
  active_q_8 (9 / 2 : ℝ) (72 / 25 : ℝ) (423 / 50 : ℝ) (-72 / 25 : ℝ) (11 / 8 : ℝ) (1573 / 944 : ℝ) (143 / 118 : ℝ) (118 / 107 : ℝ)
    (188009674597 / 125000000000 : ℝ) (3760193491941 / 2500000000000 : ℝ) (96080002897 / 500000000000 : ℝ) (240200007243 / 1250000000000 : ℝ) (489278950017 / 5000000000000 : ℝ) (978557900041 / 10000000000000 : ℝ)
    (338140989871 / 1250000000000 : ℝ) (2705127964143 / 10000000000000 : ℝ) (1372695062081 / 10000000000000 : ℝ) (686347540753 / 5000000000000 : ℝ) (56847797203 / 10000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog_108 hlog_138 hlog_139 hqchain_144 hqchain_147 (by norm_num)

private lemma hterm_137 :
    IntervalIntegrable (fun t => ind (11 / 8 : ℝ) (1573 / 944 : ℝ) t / (5 * t * (1 - t / (9 / 2 : ℝ))) * Real.log ((9 / 2 : ℝ) / ((72 / 25 : ℝ) * (9 / 2 : ℝ) - (9 / 2 : ℝ) - (72 / 25 : ℝ) * t))) volume (1 : ℝ) (11 / 5 : ℝ) ∧
      (56847797203 / 10000000000000 : ℝ) ≤ ∫ t in (1 : ℝ)..(11 / 5 : ℝ), ind (11 / 8 : ℝ) (1573 / 944 : ℝ) t / (5 * t * (1 - t / (9 / 2 : ℝ))) * Real.log ((9 / 2 : ℝ) / ((72 / 25 : ℝ) * (9 / 2 : ℝ) - (9 / 2 : ℝ) - (72 / 25 : ℝ) * t)) :=
  bound_ind_div_active (1 : ℝ) (11 / 5 : ℝ) (11 / 8 : ℝ) (1573 / 944 : ℝ) (11 / 8 : ℝ) (1573 / 944 : ℝ) (56847797203 / 10000000000000 : ℝ)
    (fun t => 5 * t * (1 - t / (9 / 2 : ℝ))) (fun t => (9 / 2 : ℝ) / ((72 / 25 : ℝ) * (9 / 2 : ℝ) - (9 / 2 : ℝ) - (72 / 25 : ℝ) * t))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (Or.inr rfl) (Or.inr rfl) hact_q8_148

private lemma hlog_150 : (5563781067767 / 10000000000000 : ℝ) ≤ Real.log (82333 / 47200 : ℝ) ∧ Real.log (82333 / 47200 : ℝ) ≤ (5433379949 / 9765625000 : ℝ) :=
  log_rat_bounds (82333 / 47200 : ℝ) (3497 / 1478497 : ℝ) (-3) (-2) (3) (5563781067767 / 10000000000000 : ℝ) (5433379949 / 9765625000 : ℝ)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hqsub_151 :
    IntervalIntegrable (fun t => Real.log ((7 / 2 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t)) volume (1573 / 944 : ℝ) (369 / 200 : ℝ) ∧
      (567197616627 / 10000000000000 : ℝ) ≤ ∫ t in (1573 / 944 : ℝ)..(369 / 200 : ℝ), Real.log ((7 / 2 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (1573 / 944 : ℝ)..(369 / 200 : ℝ), Real.log ((7 / 2 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ≤ (113439527313 / 2000000000000 : ℝ) :=
  quad_log_div_sub (7 / 2 : ℝ) (-1 : ℝ) (0 : ℝ) (1 : ℝ) (1573 / 944 : ℝ) (369 / 200 : ℝ) (82867 / 47200 : ℝ) (4217 / 47200 : ℝ)
    (82333 / 47200 : ℝ) (82867 / 47200 : ℝ) (-47200 / 82333 : ℝ) (47200 / 82867 : ℝ) (47200 / 82333 : ℝ) (5563781067767 / 10000000000000 : ℝ) (5433379949 / 9765625000 : ℝ) (567197616627 / 10000000000000 : ℝ) (113439527313 / 2000000000000 : ℝ)
    hlog_150 (by norm_num [quadLogLo, quadLogHi])

private lemma hlog_152 : (2247409967623 / 5000000000000 : ℝ) ≤ Real.log (627 / 400 : ℝ) ∧ Real.log (627 / 400 : ℝ) ≤ (1123704983813 / 2500000000000 : ℝ) :=
  log_rat_bounds (627 / 400 : ℝ) (1 / 626 : ℝ) (-4) (0) (2) (2247409967623 / 5000000000000 : ℝ) (1123704983813 / 2500000000000 : ℝ)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hqsub_153 :
    IntervalIntegrable (fun t => Real.log ((7 / 2 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t)) volume (369 / 200 : ℝ) (101 / 50 : ℝ) ∧
      (101901416513 / 2500000000000 : ℝ) ≤ ∫ t in (369 / 200 : ℝ)..(101 / 50 : ℝ), Real.log ((7 / 2 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (369 / 200 : ℝ)..(101 / 50 : ℝ), Real.log ((7 / 2 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ≤ (50950711751 / 1250000000000 : ℝ) :=
  quad_log_div_sub (7 / 2 : ℝ) (-1 : ℝ) (0 : ℝ) (1 : ℝ) (369 / 200 : ℝ) (101 / 50 : ℝ) (773 / 400 : ℝ) (7 / 80 : ℝ)
    (627 / 400 : ℝ) (773 / 400 : ℝ) (-400 / 627 : ℝ) (400 / 773 : ℝ) (400 / 627 : ℝ) (2247409967623 / 5000000000000 : ℝ) (1123704983813 / 2500000000000 : ℝ) (101901416513 / 2500000000000 : ℝ) (50950711751 / 1250000000000 : ℝ)
    hlog_152 (by norm_num [quadLogLo, quadLogHi])

private lemma hlog_154 : (3293037471423 / 10000000000000 : ℝ) ≤ Real.log (139 / 100 : ℝ) ∧ Real.log (139 / 100 : ℝ) ≤ (3293037471429 / 10000000000000 : ℝ) :=
  log_rat_bounds (139 / 100 : ℝ) (1 / 2501 : ℝ) (-1) (-2) (2) (3293037471423 / 10000000000000 : ℝ) (3293037471429 / 10000000000000 : ℝ)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hqsub_155 :
    IntervalIntegrable (fun t => Real.log ((7 / 2 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t)) volume (101 / 50 : ℝ) (11 / 5 : ℝ) ∧
      (56256507397 / 2000000000000 : ℝ) ≤ ∫ t in (101 / 50 : ℝ)..(11 / 5 : ℝ), Real.log ((7 / 2 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (101 / 50 : ℝ)..(11 / 5 : ℝ), Real.log ((7 / 2 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ≤ (281282600113 / 10000000000000 : ℝ) :=
  quad_log_div_sub (7 / 2 : ℝ) (-1 : ℝ) (0 : ℝ) (1 : ℝ) (101 / 50 : ℝ) (11 / 5 : ℝ) (211 / 100 : ℝ) (9 / 100 : ℝ)
    (139 / 100 : ℝ) (211 / 100 : ℝ) (-100 / 139 : ℝ) (100 / 211 : ℝ) (100 / 139 : ℝ) (3293037471423 / 10000000000000 : ℝ) (3293037471429 / 10000000000000 : ℝ) (56256507397 / 2000000000000 : ℝ) (281282600113 / 10000000000000 : ℝ)
    hlog_154 (by norm_num [quadLogLo, quadLogHi])

private lemma hqchain_156 :
    IntervalIntegrable (fun t => Real.log ((7 / 2 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t)) volume (1573 / 944 : ℝ) (101 / 50 : ℝ) ∧
      (974803282679 / 10000000000000 : ℝ) ≤ ∫ t in (1573 / 944 : ℝ)..(101 / 50 : ℝ), Real.log ((7 / 2 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (1573 / 944 : ℝ)..(101 / 50 : ℝ), Real.log ((7 / 2 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ≤ (974803330573 / 10000000000000 : ℝ) :=
  chain_int_bounds hqsub_151 hqsub_153 (by norm_num)

private lemma hqchain_157 :
    IntervalIntegrable (fun t => Real.log ((7 / 2 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t)) volume (1573 / 944 : ℝ) (11 / 5 : ℝ) ∧
      (78505363729 / 625000000000 : ℝ) ≤ ∫ t in (1573 / 944 : ℝ)..(11 / 5 : ℝ), Real.log ((7 / 2 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (1573 / 944 : ℝ)..(11 / 5 : ℝ), Real.log ((7 / 2 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ≤ (628042965343 / 5000000000000 : ℝ) :=
  chain_int_bounds hqchain_156 hqsub_155 (by norm_num)

private lemma hlog_158 : (5302418354359 / 10000000000000 : ℝ) ≤ Real.log (80209 / 47200 : ℝ) ∧ Real.log (80209 / 47200 : ℝ) ≤ (1060483670873 / 2000000000000 : ℝ) :=
  log_rat_bounds (80209 / 47200 : ℝ) (559 / 159859 : ℝ) (-4) (3) (0) (5302418354359 / 10000000000000 : ℝ) (1060483670873 / 2000000000000 : ℝ)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hqsub_159 :
    IntervalIntegrable (fun t => Real.log ((7 / 2 : ℝ) + (-1 : ℝ) * t) / ((9 / 2 : ℝ) + (-1 : ℝ) * t)) volume (1573 / 944 : ℝ) (387 / 200 : ℝ) ∧
      (525877543391 / 10000000000000 : ℝ) ≤ ∫ t in (1573 / 944 : ℝ)..(387 / 200 : ℝ), Real.log ((7 / 2 : ℝ) + (-1 : ℝ) * t) / ((9 / 2 : ℝ) + (-1 : ℝ) * t) ∧
      ∫ t in (1573 / 944 : ℝ)..(387 / 200 : ℝ), Real.log ((7 / 2 : ℝ) + (-1 : ℝ) * t) / ((9 / 2 : ℝ) + (-1 : ℝ) * t) ≤ (525877787659 / 10000000000000 : ℝ) :=
  quad_log_div_sub (7 / 2 : ℝ) (-1 : ℝ) (9 / 2 : ℝ) (-1 : ℝ) (1573 / 944 : ℝ) (387 / 200 : ℝ) (84991 / 47200 : ℝ) (6341 / 47200 : ℝ)
    (80209 / 47200 : ℝ) (127409 / 47200 : ℝ) (-47200 / 80209 : ℝ) (-47200 / 127409 : ℝ) (47200 / 80209 : ℝ) (5302418354359 / 10000000000000 : ℝ) (1060483670873 / 2000000000000 : ℝ) (525877543391 / 10000000000000 : ℝ) (525877787659 / 10000000000000 : ℝ)
    hlog_158 (by norm_num [quadLogLo, quadLogHi])

private lemma hlog_160 : (4037970510071 / 10000000000000 : ℝ) ≤ Real.log (599 / 400 : ℝ) ∧ Real.log (599 / 400 : ℝ) ≤ (2018985255039 / 5000000000000 : ℝ) :=
  log_rat_bounds (599 / 400 : ℝ) (173 / 32173 : ℝ) (3) (-3) (1) (4037970510071 / 10000000000000 : ℝ) (2018985255039 / 5000000000000 : ℝ)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hqsub_161 :
    IntervalIntegrable (fun t => Real.log ((7 / 2 : ℝ) + (-1 : ℝ) * t) / ((9 / 2 : ℝ) + (-1 : ℝ) * t)) volume (387 / 200 : ℝ) (207 / 100 : ℝ) ∧
      (108959459809 / 5000000000000 : ℝ) ≤ ∫ t in (387 / 200 : ℝ)..(207 / 100 : ℝ), Real.log ((7 / 2 : ℝ) + (-1 : ℝ) * t) / ((9 / 2 : ℝ) + (-1 : ℝ) * t) ∧
      ∫ t in (387 / 200 : ℝ)..(207 / 100 : ℝ), Real.log ((7 / 2 : ℝ) + (-1 : ℝ) * t) / ((9 / 2 : ℝ) + (-1 : ℝ) * t) ≤ (217918924167 / 10000000000000 : ℝ) :=
  quad_log_div_sub (7 / 2 : ℝ) (-1 : ℝ) (9 / 2 : ℝ) (-1 : ℝ) (387 / 200 : ℝ) (207 / 100 : ℝ) (801 / 400 : ℝ) (27 / 400 : ℝ)
    (599 / 400 : ℝ) (999 / 400 : ℝ) (-400 / 599 : ℝ) (-400 / 999 : ℝ) (400 / 599 : ℝ) (4037970510071 / 10000000000000 : ℝ) (2018985255039 / 5000000000000 : ℝ) (108959459809 / 5000000000000 : ℝ) (217918924167 / 10000000000000 : ℝ)
    hlog_160 (by norm_num [quadLogLo, quadLogHi])

private lemma hlog_162 : (1555772143183 / 5000000000000 : ℝ) ≤ Real.log (273 / 200 : ℝ) ∧ Real.log (273 / 200 : ℝ) ≤ (777886071593 / 2500000000000 : ℝ) :=
  log_rat_bounds (273 / 200 : ℝ) (1 / 181 : ℝ) (-2) (3) (-1) (1555772143183 / 5000000000000 : ℝ) (777886071593 / 2500000000000 : ℝ)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hqsub_163 :
    IntervalIntegrable (fun t => Real.log ((7 / 2 : ℝ) + (-1 : ℝ) * t) / ((9 / 2 : ℝ) + (-1 : ℝ) * t)) volume (207 / 100 : ℝ) (11 / 5 : ℝ) ∧
      (21328918301 / 1250000000000 : ℝ) ≤ ∫ t in (207 / 100 : ℝ)..(11 / 5 : ℝ), Real.log ((7 / 2 : ℝ) + (-1 : ℝ) * t) / ((9 / 2 : ℝ) + (-1 : ℝ) * t) ∧
      ∫ t in (207 / 100 : ℝ)..(11 / 5 : ℝ), Real.log ((7 / 2 : ℝ) + (-1 : ℝ) * t) / ((9 / 2 : ℝ) + (-1 : ℝ) * t) ≤ (17063135283 / 1000000000000 : ℝ) :=
  quad_log_div_sub (7 / 2 : ℝ) (-1 : ℝ) (9 / 2 : ℝ) (-1 : ℝ) (207 / 100 : ℝ) (11 / 5 : ℝ) (427 / 200 : ℝ) (13 / 200 : ℝ)
    (273 / 200 : ℝ) (473 / 200 : ℝ) (-200 / 273 : ℝ) (-200 / 473 : ℝ) (200 / 273 : ℝ) (1555772143183 / 5000000000000 : ℝ) (777886071593 / 2500000000000 : ℝ) (21328918301 / 1250000000000 : ℝ) (17063135283 / 1000000000000 : ℝ)
    hlog_162 (by norm_num [quadLogLo, quadLogHi])

private lemma hqchain_164 :
    IntervalIntegrable (fun t => Real.log ((7 / 2 : ℝ) + (-1 : ℝ) * t) / ((9 / 2 : ℝ) + (-1 : ℝ) * t)) volume (1573 / 944 : ℝ) (207 / 100 : ℝ) ∧
      (743796463009 / 10000000000000 : ℝ) ≤ ∫ t in (1573 / 944 : ℝ)..(207 / 100 : ℝ), Real.log ((7 / 2 : ℝ) + (-1 : ℝ) * t) / ((9 / 2 : ℝ) + (-1 : ℝ) * t) ∧
      ∫ t in (1573 / 944 : ℝ)..(207 / 100 : ℝ), Real.log ((7 / 2 : ℝ) + (-1 : ℝ) * t) / ((9 / 2 : ℝ) + (-1 : ℝ) * t) ≤ (371898355913 / 5000000000000 : ℝ) :=
  chain_int_bounds hqsub_159 hqsub_161 (by norm_num)

private lemma hqchain_165 :
    IntervalIntegrable (fun t => Real.log ((7 / 2 : ℝ) + (-1 : ℝ) * t) / ((9 / 2 : ℝ) + (-1 : ℝ) * t)) volume (1573 / 944 : ℝ) (11 / 5 : ℝ) ∧
      (914427809417 / 10000000000000 : ℝ) ≤ ∫ t in (1573 / 944 : ℝ)..(11 / 5 : ℝ), Real.log ((7 / 2 : ℝ) + (-1 : ℝ) * t) / ((9 / 2 : ℝ) + (-1 : ℝ) * t) ∧
      ∫ t in (1573 / 944 : ℝ)..(11 / 5 : ℝ), Real.log ((7 / 2 : ℝ) + (-1 : ℝ) * t) / ((9 / 2 : ℝ) + (-1 : ℝ) * t) ≤ (57151754041 / 625000000000 : ℝ) :=
  chain_int_bounds hqchain_164 hqsub_163 (by norm_num)

private lemma hact_q9_166 :
    IntervalIntegrable (fun t => Real.log ((9 / 2 : ℝ) - 1 - t) / (5 * t * (1 - t / (9 / 2 : ℝ)))) volume (1573 / 944 : ℝ) (11 / 5 : ℝ) ∧
      (54262840727 / 1250000000000 : ℝ) ≤ ∫ t in (1573 / 944 : ℝ)..(11 / 5 : ℝ), Real.log ((9 / 2 : ℝ) - 1 - t) / (5 * t * (1 - t / (9 / 2 : ℝ))) :=
  active_q_9 (9 / 2 : ℝ) (7 / 2 : ℝ) (1573 / 944 : ℝ) (11 / 5 : ℝ)
    (78505363729 / 625000000000 : ℝ) (628042965343 / 5000000000000 : ℝ) (914427809417 / 10000000000000 : ℝ) (57151754041 / 625000000000 : ℝ) (54262840727 / 1250000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hqchain_157 hqchain_165 (by norm_num)

private lemma hterm_149 :
    IntervalIntegrable (fun t => ind (1573 / 944 : ℝ) (5 / 2 : ℝ) t / (5 * t * (1 - t / (9 / 2 : ℝ))) * Real.log ((9 / 2 : ℝ) - 1 - t)) volume (1 : ℝ) (11 / 5 : ℝ) ∧
      (54262840727 / 1250000000000 : ℝ) ≤ ∫ t in (1 : ℝ)..(11 / 5 : ℝ), ind (1573 / 944 : ℝ) (5 / 2 : ℝ) t / (5 * t * (1 - t / (9 / 2 : ℝ))) * Real.log ((9 / 2 : ℝ) - 1 - t) :=
  bound_ind_div_active (1 : ℝ) (11 / 5 : ℝ) (1573 / 944 : ℝ) (5 / 2 : ℝ) (1573 / 944 : ℝ) (11 / 5 : ℝ) (54262840727 / 1250000000000 : ℝ)
    (fun t => 5 * t * (1 - t / (9 / 2 : ℝ))) (fun t => (9 / 2 : ℝ) - 1 - t)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (Or.inr rfl) (Or.inl rfl) hact_q9_166

private lemma hsum_all_167 :
    IntervalIntegrable (fun t => (((((((((sigma0 t / ((5 : ℝ) * t) * Real.log (2560000000 / 77674597 : ℝ)) + (ind (5 / 2 : ℝ) (3 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) ^ (5 : ℕ) / (77674597 / 2500000 : ℝ)))) + (ind (1573 / 1200 : ℝ) (77 / 50 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) / ((47 / 25 : ℝ) * ((127 / 50 : ℝ) - t))))) + (ind (89 / 54 : ℝ) (5 / 2 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) / ((143 / 100 : ℝ) * ((7 / 2 : ℝ) - t))))) + (ind (71 / 46 : ℝ) (5 / 2 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) / ((13 / 10 : ℝ) * ((7 / 2 : ℝ) - t))))) + (ind (77 / 50 : ℝ) (5 / 2 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) ^ (2 : ℕ) / (5969 / 1250 : ℝ)))) + (ind (4387 / 3186 : ℝ) (89 / 54 : ℝ) t / (5 * t * (1 - t / (9 / 2 : ℝ))) * Real.log ((9 / 2 : ℝ) ^ (2 : ℕ) / (((177 / 50 : ℝ) * (9 / 2 : ℝ) - (9 / 2 : ℝ) - (177 / 50 : ℝ) * t) * ((243 / 100 : ℝ) * (9 / 2 : ℝ) - (9 / 2 : ℝ) - (243 / 100 : ℝ) * t))))) + (ind (89 / 54 : ℝ) (1573 / 944 : ℝ) t / (5 * t * (1 - t / (9 / 2 : ℝ))) * Real.log ((9 / 2 : ℝ) * ((9 / 2 : ℝ) - 1 - t) / ((177 / 50 : ℝ) * (9 / 2 : ℝ) - (9 / 2 : ℝ) - (177 / 50 : ℝ) * t)))) + (ind (11 / 8 : ℝ) (1573 / 944 : ℝ) t / (5 * t * (1 - t / (9 / 2 : ℝ))) * Real.log ((9 / 2 : ℝ) / ((72 / 25 : ℝ) * (9 / 2 : ℝ) - (9 / 2 : ℝ) - (72 / 25 : ℝ) * t)))) + (ind (1573 / 944 : ℝ) (5 / 2 : ℝ) t / (5 * t * (1 - t / (9 / 2 : ℝ))) * Real.log ((9 / 2 : ℝ) - 1 - t))) volume (1 : ℝ) (11 / 5 : ℝ) ∧
      (1537386559477 / 10000000000000 : ℝ) ≤ ∫ t in (1 : ℝ)..(11 / 5 : ℝ), ((((((((((sigma0 t / ((5 : ℝ) * t) * Real.log (2560000000 / 77674597 : ℝ)) + (ind (5 / 2 : ℝ) (3 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) ^ (5 : ℕ) / (77674597 / 2500000 : ℝ)))) + (ind (1573 / 1200 : ℝ) (77 / 50 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) / ((47 / 25 : ℝ) * ((127 / 50 : ℝ) - t))))) + (ind (89 / 54 : ℝ) (5 / 2 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) / ((143 / 100 : ℝ) * ((7 / 2 : ℝ) - t))))) + (ind (71 / 46 : ℝ) (5 / 2 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) / ((13 / 10 : ℝ) * ((7 / 2 : ℝ) - t))))) + (ind (77 / 50 : ℝ) (5 / 2 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) ^ (2 : ℕ) / (5969 / 1250 : ℝ)))) + (ind (4387 / 3186 : ℝ) (89 / 54 : ℝ) t / (5 * t * (1 - t / (9 / 2 : ℝ))) * Real.log ((9 / 2 : ℝ) ^ (2 : ℕ) / (((177 / 50 : ℝ) * (9 / 2 : ℝ) - (9 / 2 : ℝ) - (177 / 50 : ℝ) * t) * ((243 / 100 : ℝ) * (9 / 2 : ℝ) - (9 / 2 : ℝ) - (243 / 100 : ℝ) * t))))) + (ind (89 / 54 : ℝ) (1573 / 944 : ℝ) t / (5 * t * (1 - t / (9 / 2 : ℝ))) * Real.log ((9 / 2 : ℝ) * ((9 / 2 : ℝ) - 1 - t) / ((177 / 50 : ℝ) * (9 / 2 : ℝ) - (9 / 2 : ℝ) - (177 / 50 : ℝ) * t)))) + (ind (11 / 8 : ℝ) (1573 / 944 : ℝ) t / (5 * t * (1 - t / (9 / 2 : ℝ))) * Real.log ((9 / 2 : ℝ) / ((72 / 25 : ℝ) * (9 / 2 : ℝ) - (9 / 2 : ℝ) - (72 / 25 : ℝ) * t)))) + (ind (1573 / 944 : ℝ) (5 / 2 : ℝ) t / (5 * t * (1 - t / (9 / 2 : ℝ))) * Real.log ((9 / 2 : ℝ) - 1 - t))) :=
  add10_int_lb hterm_s0_41 hterm_42 hterm_43 hterm_57 hterm_77 hterm_97 hterm_107 hterm_127 hterm_137 hterm_149 (by norm_num)


private lemma hkern_eq (t : ℝ) : tableKernel 1 t = ((((((((((sigma0 t / ((5 : ℝ) * t) * Real.log (2560000000 / 77674597 : ℝ)) + (ind (5 / 2 : ℝ) (3 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) ^ (5 : ℕ) / (77674597 / 2500000 : ℝ)))) + (ind (1573 / 1200 : ℝ) (77 / 50 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) / ((47 / 25 : ℝ) * ((127 / 50 : ℝ) - t))))) + (ind (89 / 54 : ℝ) (5 / 2 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) / ((143 / 100 : ℝ) * ((7 / 2 : ℝ) - t))))) + (ind (71 / 46 : ℝ) (5 / 2 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) / ((13 / 10 : ℝ) * ((7 / 2 : ℝ) - t))))) + (ind (77 / 50 : ℝ) (5 / 2 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) ^ (2 : ℕ) / (5969 / 1250 : ℝ)))) + (ind (4387 / 3186 : ℝ) (89 / 54 : ℝ) t / (5 * t * (1 - t / (9 / 2 : ℝ))) * Real.log ((9 / 2 : ℝ) ^ (2 : ℕ) / (((177 / 50 : ℝ) * (9 / 2 : ℝ) - (9 / 2 : ℝ) - (177 / 50 : ℝ) * t) * ((243 / 100 : ℝ) * (9 / 2 : ℝ) - (9 / 2 : ℝ) - (243 / 100 : ℝ) * t))))) + (ind (89 / 54 : ℝ) (1573 / 944 : ℝ) t / (5 * t * (1 - t / (9 / 2 : ℝ))) * Real.log ((9 / 2 : ℝ) * ((9 / 2 : ℝ) - 1 - t) / ((177 / 50 : ℝ) * (9 / 2 : ℝ) - (9 / 2 : ℝ) - (177 / 50 : ℝ) * t)))) + (ind (11 / 8 : ℝ) (1573 / 944 : ℝ) t / (5 * t * (1 - t / (9 / 2 : ℝ))) * Real.log ((9 / 2 : ℝ) / ((72 / 25 : ℝ) * (9 / 2 : ℝ) - (9 / 2 : ℝ) - (72 / 25 : ℝ) * t)))) + (ind (1573 / 944 : ℝ) (5 / 2 : ℝ) t / (5 * t * (1 - t / (9 / 2 : ℝ))) * Real.log ((9 / 2 : ℝ) - 1 - t))) := by
  have hs : (tableParams ⟨(1 : Fin 9).val, by omega⟩).s = (23 / 10 : ℝ) := by simp [tableParams]; try norm_num
  have hsp : (tableParams ⟨(1 : Fin 9).val, by omega⟩).sp = (9 / 2 : ℝ) := by simp [tableParams]; try norm_num
  have hk1 : (tableParams ⟨(1 : Fin 9).val, by omega⟩).k1 = (177 / 50 : ℝ) := by simp [tableParams]; try norm_num
  have hk2 : (tableParams ⟨(1 : Fin 9).val, by omega⟩).k2 = (72 / 25 : ℝ) := by simp [tableParams]; try norm_num
  have hk3 : (tableParams ⟨(1 : Fin 9).val, by omega⟩).k3 = (243 / 100 : ℝ) := by simp [tableParams]; try norm_num
  have ha0 : alpha (tableParams ⟨(1 : Fin 9).val, by omega⟩) 0 = (77 / 50 : ℝ) := by simp [alpha, tableParams]; try norm_num
  have ha1 : alpha (tableParams ⟨(1 : Fin 9).val, by omega⟩) 1 = (5 / 2 : ℝ) := by simp [alpha, tableParams]; try norm_num
  have ha2 : alpha (tableParams ⟨(1 : Fin 9).val, by omega⟩) 2 = (71 / 46 : ℝ) := by simp [alpha, tableParams]; try norm_num
  have ha4 : alpha (tableParams ⟨(1 : Fin 9).val, by omega⟩) 4 = (89 / 54 : ℝ) := by simp [alpha, tableParams]; try norm_num
  have ha5 : alpha (tableParams ⟨(1 : Fin 9).val, by omega⟩) 5 = (11 / 8 : ℝ) := by simp [alpha, tableParams]; try norm_num
  have ha6 : alpha (tableParams ⟨(1 : Fin 9).val, by omega⟩) 6 = (4387 / 3186 : ℝ) := by simp [alpha, tableParams]; try norm_num
  have ha7 : alpha (tableParams ⟨(1 : Fin 9).val, by omega⟩) 7 = (1573 / 944 : ℝ) := by simp [alpha, tableParams]; try norm_num
  have ha8 : alpha (tableParams ⟨(1 : Fin 9).val, by omega⟩) 8 = (1573 / 1200 : ℝ) := by simp [alpha, tableParams]; try norm_num
  unfold tableKernel
  rw [dif_pos (by decide)]
  unfold Xi2
  dsimp only
  rw [ha0, ha1, ha2, ha4, ha5, ha6, ha7, ha8, hs, hsp, hk1, hk2, hk3]
  rw [(show (1024 : ℝ) / (((23 / 10 : ℝ) - 1) * ((9 / 2 : ℝ) - 1) * ((177 / 50 : ℝ) - 1) * ((72 / 25 : ℝ) - 1) * ((243 / 100 : ℝ) - 1)) = (2560000000 / 77674597 : ℝ) by norm_num),
      (show ((23 / 10 : ℝ) - 1) * ((9 / 2 : ℝ) - 1) * ((177 / 50 : ℝ) - 1) * ((72 / 25 : ℝ) - 1) * ((243 / 100 : ℝ) - 1) = (77674597 / 2500000 : ℝ) by norm_num),
      (show ((177 / 50 : ℝ) - 1) * ((72 / 25 : ℝ) - 1) = (5969 / 1250 : ℝ) by norm_num),
      (show (72 / 25 : ℝ) - 1 = (47 / 25 : ℝ) by norm_num),
      (show (177 / 50 : ℝ) - 1 = (127 / 50 : ℝ) by norm_num),
      (show (243 / 100 : ℝ) - 1 = (143 / 100 : ℝ) by norm_num),
      (show (9 / 2 : ℝ) - 1 = (7 / 2 : ℝ) by norm_num),
      (show (23 / 10 : ℝ) - 1 = (13 / 10 : ℝ) by norm_num)]



theorem main_thm : (candidateMatrixQ 1 0 : ℝ) ≤ integralMatrix 1 0 := by
  have hcand : (candidateMatrixQ 1 0 : ℝ) = (768693 / 5000000 : ℝ) := by simp [candidateMatrixQ]; try norm_num
  have hga : grid ⟨(0 : Fin 9).val, by omega⟩ = (1 : ℝ) := by simp [grid]; try norm_num
  have hgb : grid ⟨(0 : Fin 9).val + 1, by omega⟩ = (11 / 5 : ℝ) := by simp [grid]; try norm_num
  unfold integralMatrix
  rw [hcand, hga, hgb]
  have hint_eq : (∫ t in (1 : ℝ)..(11 / 5 : ℝ), tableKernel 1 t) =
      ∫ t in (1 : ℝ)..(11 / 5 : ℝ), ((((((((((sigma0 t / ((5 : ℝ) * t) * Real.log (2560000000 / 77674597 : ℝ)) + (ind (5 / 2 : ℝ) (3 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) ^ (5 : ℕ) / (77674597 / 2500000 : ℝ)))) + (ind (1573 / 1200 : ℝ) (77 / 50 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) / ((47 / 25 : ℝ) * ((127 / 50 : ℝ) - t))))) + (ind (89 / 54 : ℝ) (5 / 2 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) / ((143 / 100 : ℝ) * ((7 / 2 : ℝ) - t))))) + (ind (71 / 46 : ℝ) (5 / 2 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) / ((13 / 10 : ℝ) * ((7 / 2 : ℝ) - t))))) + (ind (77 / 50 : ℝ) (5 / 2 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) ^ (2 : ℕ) / (5969 / 1250 : ℝ)))) + (ind (4387 / 3186 : ℝ) (89 / 54 : ℝ) t / (5 * t * (1 - t / (9 / 2 : ℝ))) * Real.log ((9 / 2 : ℝ) ^ (2 : ℕ) / (((177 / 50 : ℝ) * (9 / 2 : ℝ) - (9 / 2 : ℝ) - (177 / 50 : ℝ) * t) * ((243 / 100 : ℝ) * (9 / 2 : ℝ) - (9 / 2 : ℝ) - (243 / 100 : ℝ) * t))))) + (ind (89 / 54 : ℝ) (1573 / 944 : ℝ) t / (5 * t * (1 - t / (9 / 2 : ℝ))) * Real.log ((9 / 2 : ℝ) * ((9 / 2 : ℝ) - 1 - t) / ((177 / 50 : ℝ) * (9 / 2 : ℝ) - (9 / 2 : ℝ) - (177 / 50 : ℝ) * t)))) + (ind (11 / 8 : ℝ) (1573 / 944 : ℝ) t / (5 * t * (1 - t / (9 / 2 : ℝ))) * Real.log ((9 / 2 : ℝ) / ((72 / 25 : ℝ) * (9 / 2 : ℝ) - (9 / 2 : ℝ) - (72 / 25 : ℝ) * t)))) + (ind (1573 / 944 : ℝ) (5 / 2 : ℝ) t / (5 * t * (1 - t / (9 / 2 : ℝ))) * Real.log ((9 / 2 : ℝ) - 1 - t))) := by
    apply integral_congr; intro t _; exact hkern_eq t
  rw [hint_eq]
  exact le_trans (by norm_num) hsum_all_167.2

end
end W5Cert_R2_entry_1_0

theorem solution : (candidateMatrixQ 1 0 : ℝ) ≤ integralMatrix 1 0 :=
  W5Cert_R2_entry_1_0.main_thm
