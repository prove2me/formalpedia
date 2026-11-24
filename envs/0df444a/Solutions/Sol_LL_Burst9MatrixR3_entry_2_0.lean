-- Prove2me | solution 1 for LL_Burst9MatrixR3.entry_2_0
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-24T01:15:11.963959+00:00
-- url     : https://prove2.me/submissions/40d3f25e-64f4-4d43-a6c6-d6d296e94cdb

import Definitions.Def_LL_Burst9MatrixR3_candidateMatrixQ
import Definitions.Def_LL_Burst9MatrixR3_integralMatrix

open Real Set intervalIntegral Filter MeasureTheory
open scoped Topology
open LL_Burst9MatrixR3

namespace W5Cert_R3_entry_2_0
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

private lemma hlog_1 : (408219945199 / 10000000000000 : ℝ) ≤ Real.log (25 / 24 : ℝ) ∧ Real.log (25 / 24 : ℝ) ≤ (204109972603 / 5000000000000 : ℝ) :=
  log_rat_bounds (25 / 24 : ℝ) (0 : ℝ) (-3) (-1) (2) (408219945199 / 10000000000000 : ℝ) (204109972603 / 5000000000000 : ℝ)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hqsub_2 :
    IntervalIntegrable (fun t => Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t)) volume (1 : ℝ) (5 / 4 : ℝ) ∧
      (46841899307 / 10000000000000 : ℝ) ≤ ∫ t in (1 : ℝ)..(5 / 4 : ℝ), Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (1 : ℝ)..(5 / 4 : ℝ), Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t) ≤ (9368389673 / 2000000000000 : ℝ) :=
  quad_log_div_sub (2 / 3 : ℝ) (1 / 3 : ℝ) (1 : ℝ) (1 : ℝ) (1 : ℝ) (5 / 4 : ℝ) (9 / 8 : ℝ) (1 / 8 : ℝ)
    (25 / 24 : ℝ) (17 / 8 : ℝ) (8 / 25 : ℝ) (8 / 17 : ℝ) (8 / 17 : ℝ) (408219945199 / 10000000000000 : ℝ) (204109972603 / 5000000000000 : ℝ) (46841899307 / 10000000000000 : ℝ) (9368389673 / 2000000000000 : ℝ)
    hlog_1 (by norm_num [quadLogLo, quadLogHi])

private lemma hlog_3 : (1177830356561 / 10000000000000 : ℝ) ≤ Real.log (9 / 8 : ℝ) ∧ Real.log (9 / 8 : ℝ) ≤ (588915178283 / 5000000000000 : ℝ) :=
  log_rat_bounds (9 / 8 : ℝ) (0 : ℝ) (-3) (2) (0) (1177830356561 / 10000000000000 : ℝ) (588915178283 / 5000000000000 : ℝ)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hqsub_4 :
    IntervalIntegrable (fun t => Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t)) volume (5 / 4 : ℝ) (3 / 2 : ℝ) ∧
      (123170351053 / 10000000000000 : ℝ) ≤ ∫ t in (5 / 4 : ℝ)..(3 / 2 : ℝ), Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (5 / 4 : ℝ)..(3 / 2 : ℝ), Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t) ≤ (123170373847 / 10000000000000 : ℝ) :=
  quad_log_div_sub (2 / 3 : ℝ) (1 / 3 : ℝ) (1 : ℝ) (1 : ℝ) (5 / 4 : ℝ) (3 / 2 : ℝ) (11 / 8 : ℝ) (1 / 8 : ℝ)
    (9 / 8 : ℝ) (19 / 8 : ℝ) (8 / 27 : ℝ) (8 / 19 : ℝ) (8 / 19 : ℝ) (1177830356561 / 10000000000000 : ℝ) (588915178283 / 5000000000000 : ℝ) (123170351053 / 10000000000000 : ℝ) (123170373847 / 10000000000000 : ℝ)
    hlog_3 (by norm_num [quadLogLo, quadLogHi])

private lemma hlog_5 : (1961148789261 / 10000000000000 : ℝ) ≤ Real.log (73 / 60 : ℝ) ∧ Real.log (73 / 60 : ℝ) ≤ (392229757853 / 2000000000000 : ℝ) :=
  log_rat_bounds (73 / 60 : ℝ) (1 / 145 : ℝ) (1) (1) (-1) (1961148789261 / 10000000000000 : ℝ) (392229757853 / 2000000000000 : ℝ)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hqsub_6 :
    IntervalIntegrable (fun t => Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t)) volume (3 / 2 : ℝ) (9 / 5 : ℝ) ∧
      (110527588229 / 5000000000000 : ℝ) ≤ ∫ t in (3 / 2 : ℝ)..(9 / 5 : ℝ), Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (3 / 2 : ℝ)..(9 / 5 : ℝ), Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t) ≤ (221055214853 / 10000000000000 : ℝ) :=
  quad_log_div_sub (2 / 3 : ℝ) (1 / 3 : ℝ) (1 : ℝ) (1 : ℝ) (3 / 2 : ℝ) (9 / 5 : ℝ) (33 / 20 : ℝ) (3 / 20 : ℝ)
    (73 / 60 : ℝ) (53 / 20 : ℝ) (20 / 73 : ℝ) (20 / 53 : ℝ) (20 / 53 : ℝ) (1961148789261 / 10000000000000 : ℝ) (392229757853 / 2000000000000 : ℝ) (110527588229 / 5000000000000 : ℝ) (221055214853 / 10000000000000 : ℝ)
    hlog_5 (by norm_num [quadLogLo, quadLogHi])

private lemma hlog_7 : (687758225611 / 2500000000000 : ℝ) ≤ Real.log (79 / 60 : ℝ) ∧ Real.log (79 / 60 : ℝ) ≤ (1375516451227 / 5000000000000 : ℝ) :=
  log_rat_bounds (79 / 60 : ℝ) (7 / 1257 : ℝ) (-5) (-1) (3) (687758225611 / 2500000000000 : ℝ) (1375516451227 / 5000000000000 : ℝ)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hqsub_8 :
    IntervalIntegrable (fun t => Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t)) volume (9 / 5 : ℝ) (21 / 10 : ℝ) ∧
      (139553437399 / 5000000000000 : ℝ) ≤ ∫ t in (9 / 5 : ℝ)..(21 / 10 : ℝ), Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (9 / 5 : ℝ)..(21 / 10 : ℝ), Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t) ≤ (279106893143 / 10000000000000 : ℝ) :=
  quad_log_div_sub (2 / 3 : ℝ) (1 / 3 : ℝ) (1 : ℝ) (1 : ℝ) (9 / 5 : ℝ) (21 / 10 : ℝ) (39 / 20 : ℝ) (3 / 20 : ℝ)
    (79 / 60 : ℝ) (59 / 20 : ℝ) (20 / 79 : ℝ) (20 / 59 : ℝ) (20 / 59 : ℝ) (687758225611 / 2500000000000 : ℝ) (1375516451227 / 5000000000000 : ℝ) (139553437399 / 5000000000000 : ℝ) (279106893143 / 10000000000000 : ℝ)
    hlog_7 (by norm_num [quadLogLo, quadLogHi])

private lemma hlog_9 : (1741533471339 / 5000000000000 : ℝ) ≤ Real.log (17 / 12 : ℝ) ∧ Real.log (17 / 12 : ℝ) ≤ (1741533471343 / 5000000000000 : ℝ) :=
  log_rat_bounds (17 / 12 : ℝ) (1 / 271 : ℝ) (-5) (2) (1) (1741533471339 / 5000000000000 : ℝ) (1741533471343 / 5000000000000 : ℝ)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hqsub_10 :
    IntervalIntegrable (fun t => Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t)) volume (21 / 10 : ℝ) (12 / 5 : ℝ) ∧
      (321048510283 / 10000000000000 : ℝ) ≤ ∫ t in (21 / 10 : ℝ)..(12 / 5 : ℝ), Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (21 / 10 : ℝ)..(12 / 5 : ℝ), Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t) ≤ (321048519701 / 10000000000000 : ℝ) :=
  quad_log_div_sub (2 / 3 : ℝ) (1 / 3 : ℝ) (1 : ℝ) (1 : ℝ) (21 / 10 : ℝ) (12 / 5 : ℝ) (9 / 4 : ℝ) (3 / 20 : ℝ)
    (17 / 12 : ℝ) (13 / 4 : ℝ) (4 / 17 : ℝ) (4 / 13 : ℝ) (4 / 13 : ℝ) (1741533471339 / 5000000000000 : ℝ) (1741533471343 / 5000000000000 : ℝ) (321048510283 / 10000000000000 : ℝ) (321048519701 / 10000000000000 : ℝ)
    hlog_9 (by norm_num [quadLogLo, quadLogHi])

private lemma hlog_11 : (2082574721473 / 5000000000000 : ℝ) ≤ Real.log (91 / 60 : ℝ) ∧ Real.log (91 / 60 : ℝ) ≤ (4165149442949 / 10000000000000 : ℝ) :=
  log_rat_bounds (91 / 60 : ℝ) (1 / 181 : ℝ) (-1) (1) (0) (2082574721473 / 5000000000000 : ℝ) (4165149442949 / 10000000000000 : ℝ)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hqsub_12 :
    IntervalIntegrable (fun t => Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t)) volume (12 / 5 : ℝ) (27 / 10 : ℝ) ∧
      (351647974639 / 10000000000000 : ℝ) ≤ ∫ t in (12 / 5 : ℝ)..(27 / 10 : ℝ), Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (12 / 5 : ℝ)..(27 / 10 : ℝ), Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t) ≤ (43955997471 / 1250000000000 : ℝ) :=
  quad_log_div_sub (2 / 3 : ℝ) (1 / 3 : ℝ) (1 : ℝ) (1 : ℝ) (12 / 5 : ℝ) (27 / 10 : ℝ) (51 / 20 : ℝ) (3 / 20 : ℝ)
    (91 / 60 : ℝ) (71 / 20 : ℝ) (20 / 91 : ℝ) (20 / 71 : ℝ) (20 / 71 : ℝ) (2082574721473 / 5000000000000 : ℝ) (4165149442949 / 10000000000000 : ℝ) (351647974639 / 10000000000000 : ℝ) (43955997471 / 1250000000000 : ℝ)
    hlog_11 (by norm_num [quadLogLo, quadLogHi])

private lemma hlog_13 : (480366416281 / 1000000000000 : ℝ) ≤ Real.log (97 / 60 : ℝ) ∧ Real.log (97 / 60 : ℝ) ≤ (960732832563 / 2000000000000 : ℝ) :=
  log_rat_bounds (97 / 60 : ℝ) (1 / 193 : ℝ) (3) (0) (-1) (480366416281 / 1000000000000 : ℝ) (960732832563 / 2000000000000 : ℝ)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hqsub_14 :
    IntervalIntegrable (fun t => Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t)) volume (27 / 10 : ℝ) (3 : ℝ) ∧
      (374063360791 / 10000000000000 : ℝ) ≤ ∫ t in (27 / 10 : ℝ)..(3 : ℝ), Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (27 / 10 : ℝ)..(3 : ℝ), Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t) ≤ (14962534549 / 400000000000 : ℝ) :=
  quad_log_div_sub (2 / 3 : ℝ) (1 / 3 : ℝ) (1 : ℝ) (1 : ℝ) (27 / 10 : ℝ) (3 : ℝ) (57 / 20 : ℝ) (3 / 20 : ℝ)
    (97 / 60 : ℝ) (77 / 20 : ℝ) (20 / 97 : ℝ) (20 / 77 : ℝ) (20 / 77 : ℝ) (480366416281 / 1000000000000 : ℝ) (960732832563 / 2000000000000 : ℝ) (374063360791 / 10000000000000 : ℝ) (14962534549 / 400000000000 : ℝ)
    hlog_13 (by norm_num [quadLogLo, quadLogHi])

private lemma hqchain_15 :
    IntervalIntegrable (fun t => Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t)) volume (1 : ℝ) (21 / 10 : ℝ) ∧
      (41885893851 / 625000000000 : ℝ) ≤ ∫ t in (1 : ℝ)..(21 / 10 : ℝ), Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (1 : ℝ)..(21 / 10 : ℝ), Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t) ≤ (654467217 / 9765625000 : ℝ) :=
  chain4_int_bounds hqsub_2 hqsub_4 hqsub_6 hqsub_8 (by norm_num)

private lemma hqchain_16 :
    IntervalIntegrable (fun t => Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t)) volume (1 : ℝ) (3 : ℝ) ∧
      (1716934147329 / 10000000000000 : ℝ) ≤ ∫ t in (1 : ℝ)..(3 : ℝ), Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (1 : ℝ)..(3 : ℝ), Real.log ((2 / 3 : ℝ) + (1 / 3 : ℝ) * t) / ((1 : ℝ) + (1 : ℝ) * t) ≤ (858467146701 / 5000000000000 : ℝ) :=
  chain4_int_bounds hqchain_15 hqsub_10 hqsub_12 hqsub_14 (by norm_num)

private lemma hfga_17 : (0 : ℝ) ≤ ∫ s in (1 : ℝ)..(1 : ℝ), Real.log ((s + 2) / 3) / (s + 1) := by
  rw [integral_same]

private lemma hlog_18 : (7884573603639 / 10000000000000 : ℝ) ≤ Real.log (11 / 5 : ℝ) ∧ Real.log (11 / 5 : ℝ) ≤ (3942286801823 / 5000000000000 : ℝ) :=
  log_rat_bounds (11 / 5 : ℝ) (1 / 109 : ℝ) (1) (3) (-2) (7884573603639 / 10000000000000 : ℝ) (3942286801823 / 5000000000000 : ℝ)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hlog_19 : (3650942261199 / 5000000000000 : ℝ) ≤ Real.log (110 / 53 : ℝ) ∧ Real.log (110 / 53 : ℝ) ≤ (7301884522407 / 10000000000000 : ℝ) :=
  log_rat_bounds (110 / 53 : ℝ) (107 / 8693 : ℝ) (-3) (4) (-1) (3650942261199 / 5000000000000 : ℝ) (7301884522407 / 10000000000000 : ℝ)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hlog_20 : (198026272957 / 10000000000000 : ℝ) ≤ Real.log (51 / 50 : ℝ) ∧ Real.log (51 / 50 : ℝ) ≤ (99013136483 / 5000000000000 : ℝ) :=
  log_rat_bounds (51 / 50 : ℝ) (1 / 271 : ℝ) (-4) (4) (-1) (198026272957 / 10000000000000 : ℝ) (99013136483 / 5000000000000 : ℝ)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hpsub_21 :
    IntervalIntegrable (fun t => Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1)) volume (1 : ℝ) (28 / 25 : ℝ) ∧
      (811374407 / 1000000000000 : ℝ) ≤ ∫ t in (1 : ℝ)..(28 / 25 : ℝ), Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1) :=
  quad_prod5_sub (11 / 5 : ℝ) (110 / 53 : ℝ) (51 / 50 : ℝ) (1 : ℝ) (28 / 25 : ℝ) (53 / 50 : ℝ) (3 / 50 : ℝ)
    (50 / 53 : ℝ) (50 / 153 : ℝ) (50 / 103 : ℝ) (722982488766439964095443 / 50000000000000000000000000 : ℝ) (59279597619933177777050017571 / 278409000000000000000000000000 : ℝ) (-2054856342539132239861598592483239 / 4650694276860000000000000000000000 : ℝ) (96310364855779758589043173959339755153 / 233063125726736833200000000000000000000 : ℝ) (-46857015509035041219124576949538373130951 / 144193048378789055543064000000000000000000 : ℝ) (5264694949274450058680224858163713009469934931 / 21678106899288752368932008795040000000000000000 : ℝ)
    (24454294308022934020683174574491139028409804793 / 133970700637604489639999814353347200000000000000 : ℝ) (-400195234375000000 / 35061985200272679549 : ℝ) (264220214843750000 / 105185955600818038647 : ℝ) (-20117187500000000 / 35061985200272679549 : ℝ) (3906250000000000 / 35061985200272679549 : ℝ) (3664573 / 20000000 : ℝ)
    (3650942261199 / 5000000000000 : ℝ) (7301884522407 / 10000000000000 : ℝ) (198026272957 / 10000000000000 : ℝ) (99013136483 / 5000000000000 : ℝ) (811374407 / 1000000000000 : ℝ)
    hlog_19 hlog_20 (by norm_num [quadProd5Lo])

private lemma hlog_22 : (1541517758593 / 2500000000000 : ℝ) ≤ Real.log (176 / 95 : ℝ) ∧ Real.log (176 / 95 : ℝ) ≤ (308303551719 / 500000000000 : ℝ) :=
  log_rat_bounds (176 / 95 : ℝ) (1 / 4751 : ℝ) (1) (-3) (2) (1541517758593 / 2500000000000 : ℝ) (308303551719 / 500000000000 : ℝ)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hlog_23 : (7578077727 / 125000000000 : ℝ) ≤ Real.log (17 / 16 : ℝ) ∧ Real.log (17 / 16 : ℝ) ≤ (606246218169 / 10000000000000 : ℝ) :=
  log_rat_bounds (17 / 16 : ℝ) (1 / 271 : ℝ) (-7) (3) (1) (7578077727 / 125000000000 : ℝ) (606246218169 / 10000000000000 : ℝ)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hpsub_24 :
    IntervalIntegrable (fun t => Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1)) volume (28 / 25 : ℝ) (251 / 200 : ℝ) ∧
      (22759600741 / 10000000000000 : ℝ) ≤ ∫ t in (28 / 25 : ℝ)..(251 / 200 : ℝ), Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1) :=
  quad_prod5_sub (11 / 5 : ℝ) (176 / 95 : ℝ) (17 / 16 : ℝ) (28 / 25 : ℝ) (251 / 200 : ℝ) (19 / 16 : ℝ) (27 / 400 : ℝ)
    (16 / 19 : ℝ) (16 / 51 : ℝ) (16 / 35 : ℝ) (11681741392168576158111 / 312500000000000000000000 : ℝ) (83001884417294274702790441 / 662402343750000000000000000 : ℝ) (-463798418292831772499503937329 / 1404085968017578125000000000000 : ℝ) (2660403027562762267671682945815403 / 8928670425996780395507812500000000 : ℝ) (-1379380389297545024704301247748375169 / 6308663697868350148200988769531250000 : ℝ) (2007468269034829047279074862193175538761 / 13372395582075318454764783382415771484375 : ℝ)
    (49051808907436171006465197795090808620176 / 468033845372636145916767418384552001953125 : ℝ) (-1754091487232 / 284772226325283 : ℝ) (16623402483712 / 12814750184637735 : ℝ) (-240518168576 / 854316678975849 : ℝ) (1099511627776 / 21357916974396225 : ℝ) (657661 / 6250000 : ℝ)
    (1541517758593 / 2500000000000 : ℝ) (308303551719 / 500000000000 : ℝ) (7578077727 / 125000000000 : ℝ) (606246218169 / 10000000000000 : ℝ) (22759600741 / 10000000000000 : ℝ)
    hlog_22 hlog_23 (by norm_num [quadProd5Lo])

private lemma hlog_25 : (250700241653 / 500000000000 : ℝ) ≤ Real.log (880 / 533 : ℝ) ∧ Real.log (880 / 533 : ℝ) ≤ (1253501208267 / 2500000000000 : ℝ) :=
  log_rat_bounds (880 / 533 : ℝ) (827 / 87173 : ℝ) (-1) (4) (-2) (250700241653 / 500000000000 : ℝ) (1253501208267 / 2500000000000 : ℝ)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hlog_26 : (525552422011 / 5000000000000 : ℝ) ≤ Real.log (1333 / 1200 : ℝ) ∧ Real.log (1333 / 1200 : ℝ) ≤ (1051104844029 / 10000000000000 : ℝ) :=
  log_rat_bounds (1333 / 1200 : ℝ) (37 / 2629 : ℝ) (0) (3) (-2) (525552422011 / 5000000000000 : ℝ) (1051104844029 / 10000000000000 : ℝ)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hpsub_27 :
    IntervalIntegrable (fun t => Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1)) volume (251 / 200 : ℝ) (141 / 100 : ℝ) ∧
      (6940618103 / 2000000000000 : ℝ) ≤ ∫ t in (251 / 200 : ℝ)..(141 / 100 : ℝ), Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1) :=
  quad_prod5_sub (11 / 5 : ℝ) (880 / 533 : ℝ) (1333 / 1200 : ℝ) (251 / 200 : ℝ) (141 / 100 : ℝ) (533 / 400 : ℝ) (31 / 400 : ℝ)
    (400 / 533 : ℝ) (400 / 1333 : ℝ) (400 / 933 : ℝ) (131756119199477136224183 / 2500000000000000000000000 : ℝ) (202929205893756984461216444513 / 4143038981250000000000000000000 : ℝ) (-1642128080797124108658914960445596857 / 6865908800062815140625000000000000000 : ℝ) (2395532641101043457238000384350531665333073 / 11378291120147062230488830195312500000000000 : ℝ) (-2727708005732205052782885423195412827245829702697 / 18856281460312002421433918296756695410156250000000 : ℝ) (2857858498949422879066327066123956734079265399639488833 / 31248923652597720327698045609756237812484120361328125000 : ℝ)
    (8640228714077546694375324200262163468158530799278977666 / 145776228839368365328711382769512849395238421485595703125 : ℝ) (-593890978856960000000000000 / 181045107130460304816334491449 : ℝ) (357441396736000000000000000 / 543135321391380914449003474347 : ℝ) (-24458035200000000000000000 / 181045107130460304816334491449 : ℝ) (4194304000000000000000000 / 181045107130460304816334491449 : ℝ) (2976437 / 50000000 : ℝ)
    (250700241653 / 500000000000 : ℝ) (1253501208267 / 2500000000000 : ℝ) (525552422011 / 5000000000000 : ℝ) (1051104844029 / 10000000000000 : ℝ) (6940618103 / 2000000000000 : ℝ)
    hlog_25 hlog_26 (by norm_num [quadProd5Lo])

private lemma hlog_28 : (779362480813 / 2000000000000 : ℝ) ≤ Real.log (220 / 149 : ℝ) ∧ Real.log (220 / 149 : ℝ) ≤ (487101550509 / 1250000000000 : ℝ) :=
  log_rat_bounds (220 / 149 : ℝ) (17 / 1358 : ℝ) (2) (2) (-2) (779362480813 / 2000000000000 : ℝ) (487101550509 / 1250000000000 : ℝ)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hlog_29 : (756447237729 / 5000000000000 : ℝ) ≤ Real.log (349 / 300 : ℝ) ∧ Real.log (349 / 300 : ℝ) ≤ (1512894475467 / 10000000000000 : ℝ) :=
  log_rat_bounds (349 / 300 : ℝ) (8 / 3133 : ℝ) (-2) (-3) (3) (756447237729 / 5000000000000 : ℝ) (1512894475467 / 10000000000000 : ℝ)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hpsub_30 :
    IntervalIntegrable (fun t => Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1)) volume (141 / 100 : ℝ) (157 / 100 : ℝ) ∧
      (235316459 / 62500000000 : ℝ) ≤ ∫ t in (141 / 100 : ℝ)..(157 / 100 : ℝ), Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1) :=
  quad_prod5_sub (11 / 5 : ℝ) (220 / 149 : ℝ) (349 / 300 : ℝ) (141 / 100 : ℝ) (157 / 100 : ℝ) (149 / 100 : ℝ) (2 / 25 : ℝ)
    (100 / 149 : ℝ) (100 / 349 : ℝ) (100 / 249 : ℝ) (589546595800614612193677 / 10000000000000000000000000 : ℝ) (-5851139445595951149561132559 / 431608300000000000000000000000 : ℝ) (-9432589687034595647806171545799441 / 55885717388667000000000000000000000 : ℝ) (1068627029901499486647043449553116731441 / 7236221842920900940830000000000000000000 : ℝ) (-89641587892968495535319373053028873151663441 / 936964022413787126862011066700000000000000000 : ℝ) (6796385504636112371477216916791100106559650595441 / 121320434662552967516039079323872083000000000000000 : ℝ)
    (10214301987884273171225182416791100106559650595441 / 302087882309756889114937307516441486670000000000000 : ℝ) (-673969130000000000000 / 380240591486107040260001 : ℝ) (385505875000000000000 / 1140721774458321120780003 : ℝ) (-24900000000000000000 / 380240591486107040260001 : ℝ) (4000000000000000000 / 380240591486107040260001 : ℝ) (679127 / 20000000 : ℝ)
    (779362480813 / 2000000000000 : ℝ) (487101550509 / 1250000000000 : ℝ) (756447237729 / 5000000000000 : ℝ) (1512894475467 / 10000000000000 : ℝ) (235316459 / 62500000000 : ℝ)
    hlog_28 hlog_29 (by norm_num [quadProd5Lo])

private lemma hlog_31 : (719205181129 / 2500000000000 : ℝ) ≤ Real.log (4 / 3 : ℝ) ∧ Real.log (4 / 3 : ℝ) ≤ (2876820724519 / 10000000000000 : ℝ) :=
  log_rat_bounds (4 / 3 : ℝ) (0 : ℝ) (2) (-1) (0) (719205181129 / 2500000000000 : ℝ) (2876820724519 / 10000000000000 : ℝ)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hpsub_32 :
    IntervalIntegrable (fun t => Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1)) volume (157 / 100 : ℝ) (173 / 100 : ℝ) ∧
      (33912241969 / 10000000000000 : ℝ) ≤ ∫ t in (157 / 100 : ℝ)..(173 / 100 : ℝ), Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1) :=
  quad_prod5_sub (11 / 5 : ℝ) (4 / 3 : ℝ) (73 / 60 : ℝ) (157 / 100 : ℝ) (173 / 100 : ℝ) (33 / 20 : ℝ) (2 / 25 : ℝ)
    (20 / 33 : ℝ) (20 / 73 : ℝ) (20 / 53 : ℝ) (1410468370201376555055669 / 25000000000000000000000000 : ℝ) (-3262710449998642873709702207 / 53198750000000000000000000000 : ℝ) (-39965574485000014523483327383337 / 339612840187500000000000000000000 : ℝ) (227403550565787340551858835666458833 / 2168037429830971875000000000000000000 : ℝ) (-2688428590912712716287958889736497986091 / 41521277239279349412656250000000000000000 : ℝ) (1044160583336591196719706891063635960943691 / 29451733967108163860887289062500000000000000 : ℝ)
    (1567132479822189537969706891063635960943691 / 78047095012836634231351316015625000000000000 : ℝ) (-9070208000000 / 9014496834354561 : ℝ) (44423360000000 / 243391414527573147 : ℝ) (-2713600000000 / 81130471509191049 : ℝ) (409600000000 / 81130471509191049 : ℝ) (20161 / 1000000 : ℝ)
    (719205181129 / 2500000000000 : ℝ) (2876820724519 / 10000000000000 : ℝ) (1961148789261 / 10000000000000 : ℝ) (392229757853 / 2000000000000 : ℝ) (33912241969 / 10000000000000 : ℝ)
    hlog_31 hlog_5 (by norm_num [quadProd5Lo])

private lemma hlog_33 : (1965126853133 / 10000000000000 : ℝ) ≤ Real.log (880 / 723 : ℝ) ∧ Real.log (880 / 723 : ℝ) ≤ (1965126853137 / 10000000000000 : ℝ) :=
  log_rat_bounds (880 / 723 : ℝ) (31 / 4369 : ℝ) (1) (1) (-1) (1965126853133 / 10000000000000 : ℝ) (1965126853137 / 10000000000000 : ℝ)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hlog_34 : (1191802585593 / 5000000000000 : ℝ) ≤ Real.log (1523 / 1200 : ℝ) ∧ Real.log (1523 / 1200 : ℝ) ≤ (476721034239 / 2000000000000 : ℝ) :=
  log_rat_bounds (1523 / 1200 : ℝ) (17 / 12167 : ℝ) (-6) (4) (0) (1191802585593 / 5000000000000 : ℝ) (476721034239 / 2000000000000 : ℝ)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hpsub_35 :
    IntervalIntegrable (fun t => Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1)) volume (173 / 100 : ℝ) (377 / 200 : ℝ) ∧
      (5154140427 / 2000000000000 : ℝ) ≤ ∫ t in (173 / 100 : ℝ)..(377 / 200 : ℝ), Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1) :=
  quad_prod5_sub (11 / 5 : ℝ) (880 / 723 : ℝ) (1523 / 1200 : ℝ) (173 / 100 : ℝ) (377 / 200 : ℝ) (723 / 400 : ℝ) (31 / 400 : ℝ)
    (400 / 723 : ℝ) (400 / 1523 : ℝ) (400 / 1123 : ℝ) (2342043264582144972712869 / 50000000000000000000000000 : ℝ) (-4994973199448618632219449576367 / 51523661125000000000000000000000 : ℝ) (-12913390315577967491945852207424581657 / 159281259343430175937500000000000000000 : ℝ) (112099620304402008540408395092732666526172259 / 1477215653395344548418518252343750000000000000 : ℝ) (-206073233173416919396124227864246618993047533380411 / 4566693524045231289919913346503196720703125000000000 : ℝ) (109796997241356479319197265758003992729772346794546194673 / 4705855391892770723081604873091908231334381684570312500000 : ℝ)
    (55058928733106562462845316023683830909924115598182064891 / 4403896337579651268350535227068510786490425526477050781250 : ℝ) (-326124731269120000000000000 / 539597275797796991477024318883 : ℝ) (507847172096000000000000000 / 4856375482180172923293218869947 : ℝ) (-29438771200000000000000000 / 1618791827393390974431072956649 : ℝ) (4194304000000000000000000 / 1618791827393390974431072956649 : ℝ) (62749 / 5000000 : ℝ)
    (1965126853133 / 10000000000000 : ℝ) (1965126853137 / 10000000000000 : ℝ) (1191802585593 / 5000000000000 : ℝ) (476721034239 / 2000000000000 : ℝ) (5154140427 / 2000000000000 : ℝ)
    hlog_33 hlog_34 (by norm_num [quadProd5Lo])

private lemma hlog_36 : (17849717139 / 156250000000 : ℝ) ≤ Real.log (176 / 157 : ℝ) ∧ Real.log (176 / 157 : ℝ) ≤ (1142381896901 / 10000000000000 : ℝ) :=
  log_rat_bounds (176 / 157 : ℝ) (7 / 1577 : ℝ) (1) (-2) (1) (17849717139 / 156250000000 : ℝ) (1142381896901 / 10000000000000 : ℝ)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hlog_37 : (695657126337 / 2500000000000 : ℝ) ≤ Real.log (317 / 240 : ℝ) ∧ Real.log (317 / 240 : ℝ) ≤ (2782628505357 / 10000000000000 : ℝ) :=
  log_rat_bounds (317 / 240 : ℝ) (9 / 1259 : ℝ) (-5) (-1) (3) (695657126337 / 2500000000000 : ℝ) (2782628505357 / 10000000000000 : ℝ)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hpsub_38 :
    IntervalIntegrable (fun t => Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1)) volume (377 / 200 : ℝ) (51 / 25 : ℝ) ∧
      (3314952947 / 2000000000000 : ℝ) ≤ ∫ t in (377 / 200 : ℝ)..(51 / 25 : ℝ), Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1) :=
  quad_prod5_sub (11 / 5 : ℝ) (176 / 157 : ℝ) (317 / 240 : ℝ) (377 / 200 : ℝ) (51 / 25 : ℝ) (157 / 80 : ℝ) (31 / 400 : ℝ)
    (80 / 157 : ℝ) (80 / 317 : ℝ) (80 / 237 : ℝ) (12417282930845037189843 / 390625000000000000000000 : ℝ) (-2374608076612349354050432089 / 19198002929687500000000000000 : ℝ) (-51285215649561632486634890120853 / 943522090210021972656250000000000 : ℝ) (2581819741831809619284547542558244319 / 46371174021316801262664794921875000000 : ℝ) (-220245341646384281256120286216714074012311 / 6836996618605738300548133878707885742187500 : ℝ) (63932385326041733337951181016701729623074824636 / 4032205243829959525337763888861541271209716796875 : ℝ)
    (1547140173161386232309832646267227673969197194176 / 191126528557540081501010008332037056255340576171875 : ℝ) (-116147955433472000000 / 305347643801416331699849 : ℝ) (57645318799360000000 / 916042931404248995099547 : ℝ) (-3180960153600000000 / 305347643801416331699849 : ℝ) (429496729600000000 / 305347643801416331699849 : ℝ) (101559 / 12500000 : ℝ)
    (17849717139 / 156250000000 : ℝ) (1142381896901 / 10000000000000 : ℝ) (695657126337 / 2500000000000 : ℝ) (2782628505357 / 10000000000000 : ℝ) (3314952947 / 2000000000000 : ℝ)
    hlog_36 hlog_37 (by norm_num [quadProd5Lo])

private lemma hlog_39 : (370412716799 / 10000000000000 : ℝ) ≤ Real.log (55 / 53 : ℝ) ∧ Real.log (55 / 53 : ℝ) ≤ (46301589601 / 1250000000000 : ℝ) :=
  log_rat_bounds (55 / 53 : ℝ) (91 / 13659 : ℝ) (7) (0) (-3) (370412716799 / 10000000000000 : ℝ) (46301589601 / 1250000000000 : ℝ)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hlog_40 : (317240874693 / 1000000000000 : ℝ) ≤ Real.log (103 / 75 : ℝ) ∧ Real.log (103 / 75 : ℝ) ≤ (396551093367 / 1250000000000 : ℝ) :=
  log_rat_bounds (103 / 75 : ℝ) (7 / 817 : ℝ) (-2) (3) (-1) (317240874693 / 1000000000000 : ℝ) (396551093367 / 1250000000000 : ℝ)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hpsub_41 :
    IntervalIntegrable (fun t => Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1)) volume (51 / 25 : ℝ) (11 / 5 : ℝ) ∧
      (748607717 / 1250000000000 : ℝ) ≤ ∫ t in (51 / 25 : ℝ)..(11 / 5 : ℝ), Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1) :=
  quad_prod5_sub (11 / 5 : ℝ) (55 / 53 : ℝ) (103 / 75 : ℝ) (51 / 25 : ℝ) (11 / 5 : ℝ) (53 / 25 : ℝ) (2 / 25 : ℝ)
    (25 / 53 : ℝ) (25 / 103 : ℝ) (25 / 78 : ℝ) (117510054274725255067707 / 10000000000000000000000000 : ℝ) (-154700208099838233757324607 / 1071200000000000000000000000 : ℝ) (-620327537459630879918764970387 / 18244764096000000000000000000000 : ℝ) (12700947548344899748764537973342633 / 310746281664199680000000000000000000 : ℝ) (-122908740005406390486108056796477433547 / 5292655529007182085734400000000000000000 : ℝ) (986342957396305700071485043248770309733073 / 90144932382492645858795159552000000000000000 : ℝ)
    (79717173660817213975788707292184826415852869 / 14906366018768983919210367583518720000000000000 : ℝ) (-1190963134765625 / 4848031930240071299 : ℝ) (9050689697265625 / 232705532651523422352 : ℝ) (-29754638671875 / 4848031930240071299 : ℝ) (3814697265625 / 4848031930240071299 : ℝ) (536777 / 100000000 : ℝ)
    (370412716799 / 10000000000000 : ℝ) (46301589601 / 1250000000000 : ℝ) (317240874693 / 1000000000000 : ℝ) (396551093367 / 1250000000000 : ℝ) (748607717 / 1250000000000 : ℝ)
    hlog_39 hlog_40 (by norm_num [quadProd5Lo])

private lemma hpchain_42 :
    IntervalIntegrable (fun t => Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1)) volume (1 : ℝ) (157 / 100 : ℝ) ∧
      (51613534383 / 5000000000000 : ℝ) ≤ ∫ t in (1 : ℝ)..(157 / 100 : ℝ), Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1) :=
  chain4_int_lb hpsub_21 hpsub_24 hpsub_27 hpsub_30 (by norm_num)

private lemma hpchain_43 :
    IntervalIntegrable (fun t => Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1)) volume (1 : ℝ) (51 / 25 : ℝ) ∧
      (35896955521 / 2000000000000 : ℝ) ≤ ∫ t in (1 : ℝ)..(51 / 25 : ℝ), Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1) :=
  chain4_int_lb hpchain_42 hpsub_32 hpsub_35 hpsub_38 (by norm_num)

private lemma hpchain_44 :
    IntervalIntegrable (fun t => Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1)) volume (1 : ℝ) (11 / 5 : ℝ) ∧
      (185473639341 / 10000000000000 : ℝ) ≤ ∫ t in (1 : ℝ)..(11 / 5 : ℝ), Real.log ((11 / 5 : ℝ) / t) * Real.log ((t + 2) / 3) / (t + 1) :=
  chain_int_lb hpchain_43 hpsub_41 (by norm_num)

private lemma hlog_45 : (34474144135133 / 10000000000000 : ℝ) ≤ Real.log (12800000000 / 407396143 : ℝ) ∧ Real.log (12800000000 / 407396143 : ℝ) ≤ (34474144135139 / 10000000000000 : ℝ) :=
  log_rat_bounds (12800000000 / 407396143 : ℝ) (2203857 / 816996143 : ℝ) (-2) (0) (3) (34474144135133 / 10000000000000 : ℝ) (34474144135139 / 10000000000000 : ℝ)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hterm_s0_46 :
    IntervalIntegrable (fun t => sigma0 t / ((5 : ℝ) * t) * Real.log (12800000000 / 407396143 : ℝ)) volume (1 : ℝ) (11 / 5 : ℝ) ∧
      (482463641 / 31250000000 : ℝ) ≤ ∫ t in (1 : ℝ)..(11 / 5 : ℝ), sigma0 t / ((5 : ℝ) * t) * Real.log (12800000000 / 407396143 : ℝ) :=
  bound_sigma0_term (5 : ℝ) (12800000000 / 407396143 : ℝ) (1 : ℝ) (11 / 5 : ℝ) (11 / 5 : ℝ)
    (1716934147329 / 10000000000000 : ℝ) (858467146701 / 5000000000000 : ℝ) (0 : ℝ) (7884573603639 / 10000000000000 : ℝ) (3942286801823 / 5000000000000 : ℝ) (185473639341 / 10000000000000 : ℝ) (34474144135133 / 10000000000000 : ℝ) (34474144135139 / 10000000000000 : ℝ) (482463641 / 31250000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hqchain_16 (by norm_num) hfga_17 hlog_18 hpchain_44.2 hlog_45
    (by norm_num) (by norm_num) (by norm_num)

private lemma hterm_47 :
    IntervalIntegrable (fun t => ind (123 / 50 : ℝ) (3 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) ^ (5 : ℕ) / (407396143 / 12500000 : ℝ))) volume (1 : ℝ) (11 / 5 : ℝ) ∧
      (0 : ℝ) ≤ ∫ t in (1 : ℝ)..(11 / 5 : ℝ), ind (123 / 50 : ℝ) (3 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) ^ (5 : ℕ) / (407396143 / 12500000 : ℝ)) :=
  bound_ind_div_zero (1 : ℝ) (11 / 5 : ℝ) (123 / 50 : ℝ) (3 : ℝ) (fun t => (5 : ℝ) * t) (fun t => (t + 1) ^ (5 : ℕ) / (407396143 / 12500000 : ℝ)) (by norm_num) (Or.inr (by norm_num))

private lemma hlog_49 : (6259384308661 / 10000000000000 : ℝ) ≤ Real.log (187 / 100 : ℝ) ∧ Real.log (187 / 100 : ℝ) ≤ (1564846077167 / 2500000000000 : ℝ) :=
  log_rat_bounds (187 / 100 : ℝ) (49 / 10049 : ℝ) (1) (-3) (2) (6259384308661 / 10000000000000 : ℝ) (1564846077167 / 2500000000000 : ℝ)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hlog_50 : (1688351549063 / 10000000000000 : ℝ) ≤ Real.log (6437 / 5437 : ℝ) ∧ Real.log (6437 / 5437 : ℝ) ≤ (1688351549071 / 10000000000000 : ℝ) :=
  log_rat_bounds (6437 / 5437 : ℝ) (4193 / 819743 : ℝ) (-6) (1) (2) (1688351549063 / 10000000000000 : ℝ) (1688351549071 / 10000000000000 : ℝ)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hlog_51 : (8704766226613 / 10000000000000 : ℝ) ≤ Real.log (9791 / 4100 : ℝ) ∧ Real.log (9791 / 4100 : ℝ) ≤ (435238311331 / 500000000000 : ℝ) :=
  log_rat_bounds (9791 / 4100 : ℝ) (1957 / 526757 : ℝ) (6) (-3) (0) (8704766226613 / 10000000000000 : ℝ) (435238311331 / 500000000000 : ℝ)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hqsub_52 :
    IntervalIntegrable (fun t => Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t)) volume (5437 / 4100 : ℝ) (29 / 20 : ℝ) ∧
      (388545697537 / 5000000000000 : ℝ) ≤ ∫ t in (5437 / 4100 : ℝ)..(29 / 20 : ℝ), Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (5437 / 4100 : ℝ)..(29 / 20 : ℝ), Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ≤ (388545701553 / 5000000000000 : ℝ) :=
  quad_log_div_sub (1 : ℝ) (1 : ℝ) (0 : ℝ) (1 : ℝ) (5437 / 4100 : ℝ) (29 / 20 : ℝ) (5691 / 4100 : ℝ) (127 / 2050 : ℝ)
    (9791 / 4100 : ℝ) (5691 / 4100 : ℝ) (4100 / 9791 : ℝ) (4100 / 5691 : ℝ) (4100 / 5691 : ℝ) (8704766226613 / 10000000000000 : ℝ) (435238311331 / 500000000000 : ℝ) (388545697537 / 5000000000000 : ℝ) (388545701553 / 5000000000000 : ℝ)
    hlog_51 (by norm_num [quadLogLo, quadLogHi])

private lemma hlog_53 : (1840565506287 / 2000000000000 : ℝ) ≤ Real.log (251 / 100 : ℝ) ∧ Real.log (251 / 100 : ℝ) ≤ (4601413765719 / 5000000000000 : ℝ) :=
  log_rat_bounds (251 / 100 : ℝ) (1 / 501 : ℝ) (-1) (0) (1) (1840565506287 / 2000000000000 : ℝ) (4601413765719 / 5000000000000 : ℝ)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hqsub_54 :
    IntervalIntegrable (fun t => Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t)) volume (29 / 20 : ℝ) (157 / 100 : ℝ) ∧
      (731408149283 / 10000000000000 : ℝ) ≤ ∫ t in (29 / 20 : ℝ)..(157 / 100 : ℝ), Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (29 / 20 : ℝ)..(157 / 100 : ℝ), Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ≤ (731408152869 / 10000000000000 : ℝ) :=
  quad_log_div_sub (1 : ℝ) (1 : ℝ) (0 : ℝ) (1 : ℝ) (29 / 20 : ℝ) (157 / 100 : ℝ) (151 / 100 : ℝ) (3 / 50 : ℝ)
    (251 / 100 : ℝ) (151 / 100 : ℝ) (100 / 251 : ℝ) (100 / 151 : ℝ) (100 / 151 : ℝ) (1840565506287 / 2000000000000 : ℝ) (4601413765719 / 5000000000000 : ℝ) (731408149283 / 10000000000000 : ℝ) (731408152869 / 10000000000000 : ℝ)
    hlog_53 (by norm_num [quadLogLo, quadLogHi])

private lemma hqchain_55 :
    IntervalIntegrable (fun t => Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t)) volume (5437 / 4100 : ℝ) (157 / 100 : ℝ) ∧
      (1508499544357 / 10000000000000 : ℝ) ≤ ∫ t in (5437 / 4100 : ℝ)..(157 / 100 : ℝ), Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (5437 / 4100 : ℝ)..(157 / 100 : ℝ), Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ≤ (60339982239 / 400000000000 : ℝ) :=
  chain_int_bounds hqsub_52 hqsub_54 (by norm_num)

private lemma hlog_56 : (417916621709 / 2500000000000 : ℝ) ≤ Real.log (2423 / 2050 : ℝ) ∧ Real.log (2423 / 2050 : ℝ) ≤ (334333297369 / 2000000000000 : ℝ) :=
  log_rat_bounds (2423 / 2050 : ℝ) (661 / 154411 : ℝ) (-6) (1) (2) (417916621709 / 2500000000000 : ℝ) (334333297369 / 2000000000000 : ℝ)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hqsub_57 :
    IntervalIntegrable (fun t => Real.log ((257 / 100 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t)) volume (5437 / 4100 : ℝ) (29 / 20 : ℝ) ∧
      (37401536127 / 2500000000000 : ℝ) ≤ ∫ t in (5437 / 4100 : ℝ)..(29 / 20 : ℝ), Real.log ((257 / 100 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (5437 / 4100 : ℝ)..(29 / 20 : ℝ), Real.log ((257 / 100 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ≤ (74803081603 / 5000000000000 : ℝ) :=
  quad_log_div_sub (257 / 100 : ℝ) (-1 : ℝ) (0 : ℝ) (1 : ℝ) (5437 / 4100 : ℝ) (29 / 20 : ℝ) (5691 / 4100 : ℝ) (127 / 2050 : ℝ)
    (2423 / 2050 : ℝ) (5691 / 4100 : ℝ) (-2050 / 2423 : ℝ) (4100 / 5691 : ℝ) (2050 / 2423 : ℝ) (417916621709 / 2500000000000 : ℝ) (334333297369 / 2000000000000 : ℝ) (37401536127 / 2500000000000 : ℝ) (74803081603 / 5000000000000 : ℝ)
    hlog_56 (by norm_num [quadLogLo, quadLogHi])

private lemma hlog_58 : (116537816247 / 2000000000000 : ℝ) ≤ Real.log (53 / 50 : ℝ) ∧ Real.log (53 / 50 : ℝ) ≤ (116537816249 / 2000000000000 : ℝ) :=
  log_rat_bounds (53 / 50 : ℝ) (17 / 6767 : ℝ) (-7) (3) (1) (116537816247 / 2000000000000 : ℝ) (116537816249 / 2000000000000 : ℝ)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hqsub_59 :
    IntervalIntegrable (fun t => Real.log ((257 / 100 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t)) volume (29 / 20 : ℝ) (157 / 100 : ℝ) ∧
      (4650236799 / 1000000000000 : ℝ) ≤ ∫ t in (29 / 20 : ℝ)..(157 / 100 : ℝ), Real.log ((257 / 100 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (29 / 20 : ℝ)..(157 / 100 : ℝ), Real.log ((257 / 100 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ≤ (46502394159 / 10000000000000 : ℝ) :=
  quad_log_div_sub (257 / 100 : ℝ) (-1 : ℝ) (0 : ℝ) (1 : ℝ) (29 / 20 : ℝ) (157 / 100 : ℝ) (151 / 100 : ℝ) (3 / 50 : ℝ)
    (53 / 50 : ℝ) (151 / 100 : ℝ) (-50 / 53 : ℝ) (100 / 151 : ℝ) (50 / 53 : ℝ) (116537816247 / 2000000000000 : ℝ) (116537816249 / 2000000000000 : ℝ) (4650236799 / 1000000000000 : ℝ) (46502394159 / 10000000000000 : ℝ)
    hlog_58 (by norm_num [quadLogLo, quadLogHi])

private lemma hqchain_60 :
    IntervalIntegrable (fun t => Real.log ((257 / 100 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t)) volume (5437 / 4100 : ℝ) (157 / 100 : ℝ) ∧
      (98054256249 / 5000000000000 : ℝ) ≤ ∫ t in (5437 / 4100 : ℝ)..(157 / 100 : ℝ), Real.log ((257 / 100 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (5437 / 4100 : ℝ)..(157 / 100 : ℝ), Real.log ((257 / 100 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ≤ (39221711473 / 2000000000000 : ℝ) :=
  chain_int_bounds hqsub_57 hqsub_59 (by norm_num)

private lemma hact_tl_61 :
    IntervalIntegrable (fun t => Real.log ((t + 1) / ((187 / 100 : ℝ) * ((257 / 100 : ℝ) - t))) / ((5 : ℝ) * t)) volume (5437 / 4100 : ℝ) (157 / 100 : ℝ) ∧
      (25558686761 / 5000000000000 : ℝ) ≤ ∫ t in (5437 / 4100 : ℝ)..(157 / 100 : ℝ), Real.log ((t + 1) / ((187 / 100 : ℝ) * ((257 / 100 : ℝ) - t))) / ((5 : ℝ) * t) :=
  active_t_lin (5 : ℝ) (187 / 100 : ℝ) (257 / 100 : ℝ) (5437 / 4100 : ℝ) (157 / 100 : ℝ) (6437 / 5437 : ℝ) (6259384308661 / 10000000000000 : ℝ) (1564846077167 / 2500000000000 : ℝ) (1688351549063 / 10000000000000 : ℝ) (1688351549071 / 10000000000000 : ℝ)
    (1508499544357 / 10000000000000 : ℝ) (60339982239 / 400000000000 : ℝ) (98054256249 / 5000000000000 : ℝ) (39221711473 / 2000000000000 : ℝ) (25558686761 / 5000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog_49 hlog_50 hqchain_55 hqchain_60 (by norm_num)

private lemma hterm_48 :
    IntervalIntegrable (fun t => ind (5437 / 4100 : ℝ) (157 / 100 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) / ((187 / 100 : ℝ) * ((257 / 100 : ℝ) - t)))) volume (1 : ℝ) (11 / 5 : ℝ) ∧
      (25558686761 / 5000000000000 : ℝ) ≤ ∫ t in (1 : ℝ)..(11 / 5 : ℝ), ind (5437 / 4100 : ℝ) (157 / 100 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) / ((187 / 100 : ℝ) * ((257 / 100 : ℝ) - t))) :=
  bound_ind_div_active (1 : ℝ) (11 / 5 : ℝ) (5437 / 4100 : ℝ) (157 / 100 : ℝ) (5437 / 4100 : ℝ) (157 / 100 : ℝ) (25558686761 / 5000000000000 : ℝ)
    (fun t => (5 : ℝ) * t) (fun t => (t + 1) / ((187 / 100 : ℝ) * ((257 / 100 : ℝ) - t)))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (Or.inr rfl) (Or.inr rfl) hact_tl_61

private lemma hlog_63 : (3364722366209 / 10000000000000 : ℝ) ≤ Real.log (7 / 5 : ℝ) ∧ Real.log (7 / 5 : ℝ) ≤ (672944473243 / 2000000000000 : ℝ) :=
  log_rat_bounds (7 / 5 : ℝ) (1 / 251 : ℝ) (-1) (-2) (2) (3364722366209 / 10000000000000 : ℝ) (672944473243 / 2000000000000 : ℝ)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hlog_64 : (1587063033049 / 5000000000000 : ℝ) ≤ Real.log (1320 / 961 : ℝ) ∧ Real.log (1320 / 961 : ℝ) ≤ (396765758263 / 1250000000000 : ℝ) :=
  log_rat_bounds (1320 / 961 : ℝ) (151 / 17449 : ℝ) (-2) (3) (-1) (1587063033049 / 5000000000000 : ℝ) (396765758263 / 1250000000000 : ℝ)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hlog_65 : (9935603673651 / 10000000000000 : ℝ) ≤ Real.log (3241 / 1200 : ℝ) ∧ Real.log (3241 / 1200 : ℝ) ≤ (9935603673657 / 10000000000000 : ℝ) :=
  log_rat_bounds (3241 / 1200 : ℝ) (1 / 6481 : ℝ) (-1) (3) (-1) (9935603673651 / 10000000000000 : ℝ) (9935603673657 / 10000000000000 : ℝ)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hqsub_66 :
    IntervalIntegrable (fun t => Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t)) volume (961 / 600 : ℝ) (9 / 5 : ℝ) ∧
      (289701160519 / 2500000000000 : ℝ) ≤ ∫ t in (961 / 600 : ℝ)..(9 / 5 : ℝ), Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (961 / 600 : ℝ)..(9 / 5 : ℝ), Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ≤ (144850586889 / 1250000000000 : ℝ) :=
  quad_log_div_sub (1 : ℝ) (1 : ℝ) (0 : ℝ) (1 : ℝ) (961 / 600 : ℝ) (9 / 5 : ℝ) (2041 / 1200 : ℝ) (119 / 1200 : ℝ)
    (3241 / 1200 : ℝ) (2041 / 1200 : ℝ) (1200 / 3241 : ℝ) (1200 / 2041 : ℝ) (1200 / 2041 : ℝ) (9935603673651 / 10000000000000 : ℝ) (9935603673657 / 10000000000000 : ℝ) (289701160519 / 2500000000000 : ℝ) (144850586889 / 1250000000000 : ℝ)
    hlog_65 (by norm_num [quadLogLo, quadLogHi])

private lemma hlog_67 : (33272210531 / 31250000000 : ℝ) ≤ Real.log (29 / 10 : ℝ) ∧ Real.log (29 / 10 : ℝ) ≤ (1330888421241 / 1250000000000 : ℝ) :=
  log_rat_bounds (29 / 10 : ℝ) (1 / 289 : ℝ) (3) (2) (-2) (33272210531 / 31250000000 : ℝ) (1330888421241 / 1250000000000 : ℝ)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hqsub_68 :
    IntervalIntegrable (fun t => Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t)) volume (9 / 5 : ℝ) (2 : ℝ) ∧
      (560468834677 / 5000000000000 : ℝ) ≤ ∫ t in (9 / 5 : ℝ)..(2 : ℝ), Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (9 / 5 : ℝ)..(2 : ℝ), Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ≤ (140117211939 / 1250000000000 : ℝ) :=
  quad_log_div_sub (1 : ℝ) (1 : ℝ) (0 : ℝ) (1 : ℝ) (9 / 5 : ℝ) (2 : ℝ) (19 / 10 : ℝ) (1 / 10 : ℝ)
    (29 / 10 : ℝ) (19 / 10 : ℝ) (10 / 29 : ℝ) (10 / 19 : ℝ) (10 / 19 : ℝ) (33272210531 / 31250000000 : ℝ) (1330888421241 / 1250000000000 : ℝ) (560468834677 / 5000000000000 : ℝ) (140117211939 / 1250000000000 : ℝ)
    hlog_67 (by norm_num [quadLogLo, quadLogHi])

private lemma hlog_69 : (5657010557453 / 5000000000000 : ℝ) ≤ Real.log (31 / 10 : ℝ) ∧ Real.log (31 / 10 : ℝ) ≤ (2262804222983 / 2000000000000 : ℝ) :=
  log_rat_bounds (31 / 10 : ℝ) (11 / 5011 : ℝ) (1) (-4) (3) (5657010557453 / 5000000000000 : ℝ) (2262804222983 / 2000000000000 : ℝ)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hqsub_70 :
    IntervalIntegrable (fun t => Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t)) volume (2 : ℝ) (11 / 5 : ℝ) ∧
      (538843758029 / 5000000000000 : ℝ) ≤ ∫ t in (2 : ℝ)..(11 / 5 : ℝ), Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (2 : ℝ)..(11 / 5 : ℝ), Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ≤ (1077687529159 / 10000000000000 : ℝ) :=
  quad_log_div_sub (1 : ℝ) (1 : ℝ) (0 : ℝ) (1 : ℝ) (2 : ℝ) (11 / 5 : ℝ) (21 / 10 : ℝ) (1 / 10 : ℝ)
    (31 / 10 : ℝ) (21 / 10 : ℝ) (10 / 31 : ℝ) (10 / 21 : ℝ) (10 / 21 : ℝ) (5657010557453 / 5000000000000 : ℝ) (2262804222983 / 2000000000000 : ℝ) (538843758029 / 5000000000000 : ℝ) (1077687529159 / 10000000000000 : ℝ)
    hlog_69 (by norm_num [quadLogLo, quadLogHi])

private lemma hqchain_71 :
    IntervalIntegrable (fun t => Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t)) volume (961 / 600 : ℝ) (2 : ℝ) ∧
      (227974231143 / 1000000000000 : ℝ) ≤ ∫ t in (961 / 600 : ℝ)..(2 : ℝ), Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (961 / 600 : ℝ)..(2 : ℝ), Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ≤ (71241949707 / 312500000000 : ℝ) :=
  chain_int_bounds hqsub_66 hqsub_68 (by norm_num)

private lemma hqchain_72 :
    IntervalIntegrable (fun t => Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t)) volume (961 / 600 : ℝ) (11 / 5 : ℝ) ∧
      (104919682109 / 312500000000 : ℝ) ≤ ∫ t in (961 / 600 : ℝ)..(11 / 5 : ℝ), Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (961 / 600 : ℝ)..(11 / 5 : ℝ), Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ≤ (3357429919783 / 10000000000000 : ℝ) :=
  chain_int_bounds hqchain_71 hqsub_70 (by norm_num)

private lemma hlog_73 : (5648402120717 / 10000000000000 : ℝ) ≤ Real.log (2111 / 1200 : ℝ) ∧ Real.log (2111 / 1200 : ℝ) ≤ (5648402120727 / 10000000000000 : ℝ) :=
  log_rat_bounds (2111 / 1200 : ℝ) (13 / 33763 : ℝ) (-7) (2) (2) (5648402120717 / 10000000000000 : ℝ) (5648402120727 / 10000000000000 : ℝ)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hqsub_74 :
    IntervalIntegrable (fun t => Real.log ((173 / 50 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t)) volume (961 / 600 : ℝ) (9 / 5 : ℝ) ∧
      (660066753867 / 10000000000000 : ℝ) ≤ ∫ t in (961 / 600 : ℝ)..(9 / 5 : ℝ), Real.log ((173 / 50 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (961 / 600 : ℝ)..(9 / 5 : ℝ), Real.log ((173 / 50 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ≤ (330033401893 / 5000000000000 : ℝ) :=
  quad_log_div_sub (173 / 50 : ℝ) (-1 : ℝ) (0 : ℝ) (1 : ℝ) (961 / 600 : ℝ) (9 / 5 : ℝ) (2041 / 1200 : ℝ) (119 / 1200 : ℝ)
    (2111 / 1200 : ℝ) (2041 / 1200 : ℝ) (-1200 / 2111 : ℝ) (1200 / 2041 : ℝ) (1200 / 2041 : ℝ) (5648402120717 / 10000000000000 : ℝ) (5648402120727 / 10000000000000 : ℝ) (660066753867 / 10000000000000 : ℝ) (330033401893 / 5000000000000 : ℝ)
    hlog_73 (by norm_num [quadLogLo, quadLogHi])

private lemma hlog_75 : (444685821261 / 1000000000000 : ℝ) ≤ Real.log (39 / 25 : ℝ) ∧ Real.log (39 / 25 : ℝ) ≤ (4446858212619 / 10000000000000 : ℝ) :=
  log_rat_bounds (39 / 25 : ℝ) (17 / 3142 : ℝ) (0) (-4) (3) (444685821261 / 1000000000000 : ℝ) (4446858212619 / 10000000000000 : ℝ)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hqsub_76 :
    IntervalIntegrable (fun t => Real.log ((173 / 50 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t)) volume (9 / 5 : ℝ) (2 : ℝ) ∧
      (14655843269 / 312500000000 : ℝ) ≤ ∫ t in (9 / 5 : ℝ)..(2 : ℝ), Real.log ((173 / 50 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (9 / 5 : ℝ)..(2 : ℝ), Real.log ((173 / 50 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ≤ (58623382403 / 1250000000000 : ℝ) :=
  quad_log_div_sub (173 / 50 : ℝ) (-1 : ℝ) (0 : ℝ) (1 : ℝ) (9 / 5 : ℝ) (2 : ℝ) (19 / 10 : ℝ) (1 / 10 : ℝ)
    (39 / 25 : ℝ) (19 / 10 : ℝ) (-25 / 39 : ℝ) (10 / 19 : ℝ) (25 / 39 : ℝ) (444685821261 / 1000000000000 : ℝ) (4446858212619 / 10000000000000 : ℝ) (14655843269 / 312500000000 : ℝ) (58623382403 / 1250000000000 : ℝ)
    hlog_75 (by norm_num [quadLogLo, quadLogHi])

private lemma hlog_77 : (3435897043897 / 10000000000000 : ℝ) ≤ Real.log (141 / 100 : ℝ) ∧ Real.log (141 / 100 : ℝ) ≤ (53685891311 / 156250000000 : ℝ) :=
  log_rat_bounds (141 / 100 : ℝ) (1 / 751 : ℝ) (-5) (2) (1) (3435897043897 / 10000000000000 : ℝ) (53685891311 / 156250000000 : ℝ)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hqsub_78 :
    IntervalIntegrable (fun t => Real.log ((173 / 50 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t)) volume (2 : ℝ) (21 / 10 : ℝ) ∧
      (167676391063 / 10000000000000 : ℝ) ≤ ∫ t in (2 : ℝ)..(21 / 10 : ℝ), Real.log ((173 / 50 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (2 : ℝ)..(21 / 10 : ℝ), Real.log ((173 / 50 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ≤ (4191909801 / 250000000000 : ℝ) :=
  quad_log_div_sub (173 / 50 : ℝ) (-1 : ℝ) (0 : ℝ) (1 : ℝ) (2 : ℝ) (21 / 10 : ℝ) (41 / 20 : ℝ) (1 / 20 : ℝ)
    (141 / 100 : ℝ) (41 / 20 : ℝ) (-100 / 141 : ℝ) (20 / 41 : ℝ) (100 / 141 : ℝ) (3435897043897 / 10000000000000 : ℝ) (53685891311 / 156250000000 : ℝ) (167676391063 / 10000000000000 : ℝ) (4191909801 / 250000000000 : ℝ)
    hlog_77 (by norm_num [quadLogLo, quadLogHi])

private lemma hlog_79 : (1350135686063 / 5000000000000 : ℝ) ≤ Real.log (131 / 100 : ℝ) ∧ Real.log (131 / 100 : ℝ) ≤ (540054274427 / 2000000000000 : ℝ) :=
  log_rat_bounds (131 / 100 : ℝ) (19 / 6269 : ℝ) (-5) (-1) (3) (1350135686063 / 5000000000000 : ℝ) (540054274427 / 2000000000000 : ℝ)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hqsub_80 :
    IntervalIntegrable (fun t => Real.log ((173 / 50 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t)) volume (21 / 10 : ℝ) (11 / 5 : ℝ) ∧
      (125641351411 / 10000000000000 : ℝ) ≤ ∫ t in (21 / 10 : ℝ)..(11 / 5 : ℝ), Real.log ((173 / 50 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (21 / 10 : ℝ)..(11 / 5 : ℝ), Real.log ((173 / 50 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ≤ (125641352853 / 10000000000000 : ℝ) :=
  quad_log_div_sub (173 / 50 : ℝ) (-1 : ℝ) (0 : ℝ) (1 : ℝ) (21 / 10 : ℝ) (11 / 5 : ℝ) (43 / 20 : ℝ) (1 / 20 : ℝ)
    (131 / 100 : ℝ) (43 / 20 : ℝ) (-100 / 131 : ℝ) (20 / 43 : ℝ) (100 / 131 : ℝ) (1350135686063 / 5000000000000 : ℝ) (540054274427 / 2000000000000 : ℝ) (125641351411 / 10000000000000 : ℝ) (125641352853 / 10000000000000 : ℝ)
    hlog_79 (by norm_num [quadLogLo, quadLogHi])

private lemma hqchain_81 :
    IntervalIntegrable (fun t => Real.log ((173 / 50 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t)) volume (961 / 600 : ℝ) (11 / 5 : ℝ) ∧
      (1422371480949 / 10000000000000 : ℝ) ≤ ∫ t in (961 / 600 : ℝ)..(11 / 5 : ℝ), Real.log ((173 / 50 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (961 / 600 : ℝ)..(11 / 5 : ℝ), Real.log ((173 / 50 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ≤ (1422371607903 / 10000000000000 : ℝ) :=
  chain4_int_bounds hqsub_74 hqsub_76 hqsub_78 hqsub_80 (by norm_num)

private lemma hact_tl_82 :
    IntervalIntegrable (fun t => Real.log ((t + 1) / ((7 / 5 : ℝ) * ((173 / 50 : ℝ) - t))) / ((5 : ℝ) * t)) volume (961 / 600 : ℝ) (11 / 5 : ℝ) ∧
      (2167632307 / 125000000000 : ℝ) ≤ ∫ t in (961 / 600 : ℝ)..(11 / 5 : ℝ), Real.log ((t + 1) / ((7 / 5 : ℝ) * ((173 / 50 : ℝ) - t))) / ((5 : ℝ) * t) :=
  active_t_lin (5 : ℝ) (7 / 5 : ℝ) (173 / 50 : ℝ) (961 / 600 : ℝ) (11 / 5 : ℝ) (1320 / 961 : ℝ) (3364722366209 / 10000000000000 : ℝ) (672944473243 / 2000000000000 : ℝ) (1587063033049 / 5000000000000 : ℝ) (396765758263 / 1250000000000 : ℝ)
    (104919682109 / 312500000000 : ℝ) (3357429919783 / 10000000000000 : ℝ) (1422371480949 / 10000000000000 : ℝ) (1422371607903 / 10000000000000 : ℝ) (2167632307 / 125000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog_63 hlog_64 hqchain_72 hqchain_81 (by norm_num)

private lemma hterm_62 :
    IntervalIntegrable (fun t => ind (961 / 600 : ℝ) (123 / 50 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) / ((7 / 5 : ℝ) * ((173 / 50 : ℝ) - t)))) volume (1 : ℝ) (11 / 5 : ℝ) ∧
      (2167632307 / 125000000000 : ℝ) ≤ ∫ t in (1 : ℝ)..(11 / 5 : ℝ), ind (961 / 600 : ℝ) (123 / 50 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) / ((7 / 5 : ℝ) * ((173 / 50 : ℝ) - t))) :=
  bound_ind_div_active (1 : ℝ) (11 / 5 : ℝ) (961 / 600 : ℝ) (123 / 50 : ℝ) (961 / 600 : ℝ) (11 / 5 : ℝ) (2167632307 / 125000000000 : ℝ)
    (fun t => (5 : ℝ) * t) (fun t => (t + 1) / ((7 / 5 : ℝ) * ((173 / 50 : ℝ) - t)))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (Or.inr rfl) (Or.inl rfl) hact_tl_82

private lemma hact_tl_84 :
    IntervalIntegrable (fun t => Real.log ((t + 1) / ((7 / 5 : ℝ) * ((173 / 50 : ℝ) - t))) / ((5 : ℝ) * t)) volume (961 / 600 : ℝ) (11 / 5 : ℝ) ∧
      (2167632307 / 125000000000 : ℝ) ≤ ∫ t in (961 / 600 : ℝ)..(11 / 5 : ℝ), Real.log ((t + 1) / ((7 / 5 : ℝ) * ((173 / 50 : ℝ) - t))) / ((5 : ℝ) * t) :=
  active_t_lin (5 : ℝ) (7 / 5 : ℝ) (173 / 50 : ℝ) (961 / 600 : ℝ) (11 / 5 : ℝ) (1320 / 961 : ℝ) (3364722366209 / 10000000000000 : ℝ) (672944473243 / 2000000000000 : ℝ) (1587063033049 / 5000000000000 : ℝ) (396765758263 / 1250000000000 : ℝ)
    (104919682109 / 312500000000 : ℝ) (3357429919783 / 10000000000000 : ℝ) (1422371480949 / 10000000000000 : ℝ) (1422371607903 / 10000000000000 : ℝ) (2167632307 / 125000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog_63 hlog_64 hqchain_72 hqchain_81 (by norm_num)

private lemma hterm_83 :
    IntervalIntegrable (fun t => ind (961 / 600 : ℝ) (123 / 50 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) / ((7 / 5 : ℝ) * ((173 / 50 : ℝ) - t)))) volume (1 : ℝ) (11 / 5 : ℝ) ∧
      (2167632307 / 125000000000 : ℝ) ≤ ∫ t in (1 : ℝ)..(11 / 5 : ℝ), ind (961 / 600 : ℝ) (123 / 50 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) / ((7 / 5 : ℝ) * ((173 / 50 : ℝ) - t))) :=
  bound_ind_div_active (1 : ℝ) (11 / 5 : ℝ) (961 / 600 : ℝ) (123 / 50 : ℝ) (961 / 600 : ℝ) (11 / 5 : ℝ) (2167632307 / 125000000000 : ℝ)
    (fun t => (5 : ℝ) * t) (fun t => (t + 1) / ((7 / 5 : ℝ) * ((173 / 50 : ℝ) - t)))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (Or.inr rfl) (Or.inl rfl) hact_tl_84

private lemma hlog_86 : (15698443297733 / 10000000000000 : ℝ) ≤ Real.log (48059 / 10000 : ℝ) ∧ Real.log (48059 / 10000 : ℝ) ≤ (7849221648869 / 5000000000000 : ℝ) :=
  log_rat_bounds (48059 / 10000 : ℝ) (59 / 96059 : ℝ) (3) (1) (-1) (15698443297733 / 10000000000000 : ℝ) (7849221648869 / 5000000000000 : ℝ)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hlog_87 : (3373817410037 / 10000000000000 : ℝ) ≤ Real.log (220 / 157 : ℝ) ∧ Real.log (220 / 157 : ℝ) ≤ (843454352511 / 2500000000000 : ℝ) :=
  log_rat_bounds (220 / 157 : ℝ) (7 / 1577 : ℝ) (-1) (-2) (2) (3373817410037 / 10000000000000 : ℝ) (843454352511 / 2500000000000 : ℝ)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hlog_88 : (9745596399977 / 10000000000000 : ℝ) ≤ Real.log (53 / 20 : ℝ) ∧ Real.log (53 / 20 : ℝ) ≤ (1949119279997 / 2000000000000 : ℝ) :=
  log_rat_bounds (53 / 20 : ℝ) (11 / 1261 : ℝ) (-4) (-1) (3) (9745596399977 / 10000000000000 : ℝ) (1949119279997 / 2000000000000 : ℝ)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hqsub_89 :
    IntervalIntegrable (fun t => Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t)) volume (157 / 100 : ℝ) (173 / 100 : ℝ) ∧
      (945147680769 / 10000000000000 : ℝ) ≤ ∫ t in (157 / 100 : ℝ)..(173 / 100 : ℝ), Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (157 / 100 : ℝ)..(173 / 100 : ℝ), Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ≤ (945147695317 / 10000000000000 : ℝ) :=
  quad_log_div_sub (1 : ℝ) (1 : ℝ) (0 : ℝ) (1 : ℝ) (157 / 100 : ℝ) (173 / 100 : ℝ) (33 / 20 : ℝ) (2 / 25 : ℝ)
    (53 / 20 : ℝ) (33 / 20 : ℝ) (20 / 53 : ℝ) (20 / 33 : ℝ) (20 / 33 : ℝ) (9745596399977 / 10000000000000 : ℝ) (1949119279997 / 2000000000000 : ℝ) (945147680769 / 10000000000000 : ℝ) (945147695317 / 10000000000000 : ℝ)
    hlog_88 (by norm_num [quadLogLo, quadLogHi])

private lemma hlog_90 : (10322944076301 / 10000000000000 : ℝ) ≤ Real.log (1123 / 400 : ℝ) ∧ Real.log (1123 / 400 : ℝ) ≤ (10322944076307 / 10000000000000 : ℝ) :=
  log_rat_bounds (1123 / 400 : ℝ) (107 / 20107 : ℝ) (0) (-2) (2) (10322944076301 / 10000000000000 : ℝ) (10322944076307 / 10000000000000 : ℝ)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hqsub_91 :
    IntervalIntegrable (fun t => Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t)) volume (173 / 100 : ℝ) (377 / 200 : ℝ) ∧
      (110665873257 / 1250000000000 : ℝ) ≤ ∫ t in (173 / 100 : ℝ)..(377 / 200 : ℝ), Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (173 / 100 : ℝ)..(377 / 200 : ℝ), Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ≤ (885326992259 / 10000000000000 : ℝ) :=
  quad_log_div_sub (1 : ℝ) (1 : ℝ) (0 : ℝ) (1 : ℝ) (173 / 100 : ℝ) (377 / 200 : ℝ) (723 / 400 : ℝ) (31 / 400 : ℝ)
    (1123 / 400 : ℝ) (723 / 400 : ℝ) (400 / 1123 : ℝ) (400 / 723 : ℝ) (400 / 723 : ℝ) (10322944076301 / 10000000000000 : ℝ) (10322944076307 / 10000000000000 : ℝ) (110665873257 / 1250000000000 : ℝ) (885326992259 / 10000000000000 : ℝ)
    hlog_90 (by norm_num [quadLogLo, quadLogHi])

private lemma hlog_92 : (10860335064607 / 10000000000000 : ℝ) ≤ Real.log (237 / 80 : ℝ) ∧ Real.log (237 / 80 : ℝ) ≤ (10860335064617 / 10000000000000 : ℝ) :=
  log_rat_bounds (237 / 80 : ℝ) (7 / 1257 : ℝ) (-7) (1) (3) (10860335064607 / 10000000000000 : ℝ) (10860335064617 / 10000000000000 : ℝ)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hqsub_93 :
    IntervalIntegrable (fun t => Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t)) volume (377 / 200 : ℝ) (51 / 25 : ℝ) ∧
      (857842793819 / 10000000000000 : ℝ) ≤ ∫ t in (377 / 200 : ℝ)..(51 / 25 : ℝ), Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (377 / 200 : ℝ)..(51 / 25 : ℝ), Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ≤ (857842797333 / 10000000000000 : ℝ) :=
  quad_log_div_sub (1 : ℝ) (1 : ℝ) (0 : ℝ) (1 : ℝ) (377 / 200 : ℝ) (51 / 25 : ℝ) (157 / 80 : ℝ) (31 / 400 : ℝ)
    (237 / 80 : ℝ) (157 / 80 : ℝ) (80 / 237 : ℝ) (80 / 157 : ℝ) (80 / 157 : ℝ) (10860335064607 / 10000000000000 : ℝ) (10860335064617 / 10000000000000 : ℝ) (857842793819 / 10000000000000 : ℝ) (857842797333 / 10000000000000 : ℝ)
    hlog_92 (by norm_num [quadLogLo, quadLogHi])

private lemma hlog_94 : (11378330018209 / 10000000000000 : ℝ) ≤ Real.log (78 / 25 : ℝ) ∧ Real.log (78 / 25 : ℝ) ≤ (5689165009109 / 5000000000000 : ℝ) :=
  log_rat_bounds (78 / 25 : ℝ) (17 / 3142 : ℝ) (1) (-4) (3) (11378330018209 / 10000000000000 : ℝ) (5689165009109 / 5000000000000 : ℝ)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hqsub_95 :
    IntervalIntegrable (fun t => Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t)) volume (51 / 25 : ℝ) (11 / 5 : ℝ) ∧
      (85882340543 / 1000000000000 : ℝ) ≤ ∫ t in (51 / 25 : ℝ)..(11 / 5 : ℝ), Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (51 / 25 : ℝ)..(11 / 5 : ℝ), Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ≤ (171764681601 / 2000000000000 : ℝ) :=
  quad_log_div_sub (1 : ℝ) (1 : ℝ) (0 : ℝ) (1 : ℝ) (51 / 25 : ℝ) (11 / 5 : ℝ) (53 / 25 : ℝ) (2 / 25 : ℝ)
    (78 / 25 : ℝ) (53 / 25 : ℝ) (25 / 78 : ℝ) (25 / 53 : ℝ) (25 / 53 : ℝ) (11378330018209 / 10000000000000 : ℝ) (5689165009109 / 5000000000000 : ℝ) (85882340543 / 1000000000000 : ℝ) (171764681601 / 2000000000000 : ℝ)
    hlog_94 (by norm_num [quadLogLo, quadLogHi])

private lemma hqchain_96 :
    IntervalIntegrable (fun t => Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t)) volume (157 / 100 : ℝ) (11 / 5 : ℝ) ∧
      (1773570433037 / 5000000000000 : ℝ) ≤ ∫ t in (157 / 100 : ℝ)..(11 / 5 : ℝ), Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (157 / 100 : ℝ)..(11 / 5 : ℝ), Real.log ((1 : ℝ) + (1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ≤ (1773570446457 / 5000000000000 : ℝ) :=
  chain4_int_bounds hqsub_89 hqsub_91 hqsub_93 hqsub_95 (by norm_num)

private lemma hact_tp_97 :
    IntervalIntegrable (fun t => Real.log ((t + 1) ^ (2 : ℕ) / (48059 / 10000 : ℝ)) / ((5 : ℝ) * t)) volume (157 / 100 : ℝ) (11 / 5 : ℝ) ∧
      (359582720259 / 10000000000000 : ℝ) ≤ ∫ t in (157 / 100 : ℝ)..(11 / 5 : ℝ), Real.log ((t + 1) ^ (2 : ℕ) / (48059 / 10000 : ℝ)) / ((5 : ℝ) * t) :=
  active_t_pow 2 (5 : ℝ) (48059 / 10000 : ℝ) (157 / 100 : ℝ) (11 / 5 : ℝ) (220 / 157 : ℝ) (15698443297733 / 10000000000000 : ℝ) (7849221648869 / 5000000000000 : ℝ) (3373817410037 / 10000000000000 : ℝ) (843454352511 / 2500000000000 : ℝ)
    (1773570433037 / 5000000000000 : ℝ) (1773570446457 / 5000000000000 : ℝ) (359582720259 / 10000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hlog_86 hlog_87 hqchain_96 (by norm_num)

private lemma hterm_85 :
    IntervalIntegrable (fun t => ind (157 / 100 : ℝ) (123 / 50 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) ^ (2 : ℕ) / (48059 / 10000 : ℝ))) volume (1 : ℝ) (11 / 5 : ℝ) ∧
      (359582720259 / 10000000000000 : ℝ) ≤ ∫ t in (1 : ℝ)..(11 / 5 : ℝ), ind (157 / 100 : ℝ) (123 / 50 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) ^ (2 : ℕ) / (48059 / 10000 : ℝ)) :=
  bound_ind_div_active (1 : ℝ) (11 / 5 : ℝ) (157 / 100 : ℝ) (123 / 50 : ℝ) (157 / 100 : ℝ) (11 / 5 : ℝ) (359582720259 / 10000000000000 : ℝ)
    (fun t => (5 : ℝ) * t) (fun t => (t + 1) ^ (2 : ℕ) / (48059 / 10000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (Or.inr rfl) (Or.inl rfl) hact_tp_97

private lemma hlog_99 : (3737871915079 / 2500000000000 : ℝ) ≤ Real.log (223 / 50 : ℝ) ∧ Real.log (223 / 50 : ℝ) ≤ (7475743830161 / 5000000000000 : ℝ) :=
  log_rat_bounds (223 / 50 : ℝ) (7 / 4007 : ℝ) (3) (-2) (1) (3737871915079 / 2500000000000 : ℝ) (7475743830161 / 5000000000000 : ℝ)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hlog_100 : (422971006547 / 2500000000000 : ℝ) ≤ Real.log (114359 / 96559 : ℝ) ∧ Real.log (114359 / 96559 : ℝ) ≤ (422971006549 / 2500000000000 : ℝ) :=
  log_rat_bounds (114359 / 96559 : ℝ) (77051 / 14560901 : ℝ) (-6) (1) (2) (422971006547 / 2500000000000 : ℝ) (422971006549 / 2500000000000 : ℝ)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hlog_101 : (209056639767 / 2500000000000 : ℝ) ≤ Real.log (44377 / 40817 : ℝ) ∧ Real.log (44377 / 40817 : ℝ) ≤ (33449062363 / 400000000000 : ℝ) :=
  log_rat_bounds (44377 / 40817 : ℝ) (3683 / 1105742 : ℝ) (0) (3) (-2) (209056639767 / 2500000000000 : ℝ) (33449062363 / 400000000000 : ℝ)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hlog_102 : (290420868157 / 156250000000 : ℝ) ≤ Real.log (128307 / 20000 : ℝ) ∧ Real.log (128307 / 20000 : ℝ) ≤ (18586935562053 / 10000000000000 : ℝ) :=
  log_rat_bounds (128307 / 20000 : ℝ) (307 / 256307 : ℝ) (5) (0) (-1) (290420868157 / 156250000000 : ℝ) (18586935562053 / 10000000000000 : ℝ)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hqsub_103 :
    IntervalIntegrable (fun t => Real.log ((57311 / 5000 : ℝ) + (-357 / 100 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t)) volume (96559 / 71400 : ℝ) (59 / 40 : ℝ) ∧
      (1613636408391 / 10000000000000 : ℝ) ≤ ∫ t in (96559 / 71400 : ℝ)..(59 / 40 : ℝ), Real.log ((57311 / 5000 : ℝ) + (-357 / 100 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (96559 / 71400 : ℝ)..(59 / 40 : ℝ), Real.log ((57311 / 5000 : ℝ) + (-357 / 100 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ≤ (12606534499 / 78125000000 : ℝ) :=
  quad_log_div_sub (57311 / 5000 : ℝ) (-357 / 100 : ℝ) (0 : ℝ) (1 : ℝ) (96559 / 71400 : ℝ) (59 / 40 : ℝ) (100937 / 71400 : ℝ) (2189 / 35700 : ℝ)
    (128307 / 20000 : ℝ) (100937 / 71400 : ℝ) (-23800 / 42769 : ℝ) (71400 / 100937 : ℝ) (71400 / 100937 : ℝ) (290420868157 / 156250000000 : ℝ) (18586935562053 / 10000000000000 : ℝ) (1613636408391 / 10000000000000 : ℝ) (12606534499 / 78125000000 : ℝ)
    hlog_102 (by norm_num [quadLogLo, quadLogHi])

private lemma hlog_104 : (2233506940189 / 1250000000000 : ℝ) ≤ Real.log (119407 / 20000 : ℝ) ∧ Real.log (119407 / 20000 : ℝ) ≤ (17868055521521 / 10000000000000 : ℝ) :=
  log_rat_bounds (119407 / 20000 : ℝ) (23989 / 6423989 : ℝ) (5) (-3) (1) (2233506940189 / 1250000000000 : ℝ) (17868055521521 / 10000000000000 : ℝ)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hqsub_105 :
    IntervalIntegrable (fun t => Real.log ((57311 / 5000 : ℝ) + (-357 / 100 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t)) volume (59 / 40 : ℝ) (961 / 600 : ℝ) ∧
      (294464531309 / 2000000000000 : ℝ) ≤ ∫ t in (59 / 40 : ℝ)..(961 / 600 : ℝ), Real.log ((57311 / 5000 : ℝ) + (-357 / 100 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (59 / 40 : ℝ)..(961 / 600 : ℝ), Real.log ((57311 / 5000 : ℝ) + (-357 / 100 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ≤ (1472322661693 / 10000000000000 : ℝ) :=
  quad_log_div_sub (57311 / 5000 : ℝ) (-357 / 100 : ℝ) (0 : ℝ) (1 : ℝ) (59 / 40 : ℝ) (961 / 600 : ℝ) (923 / 600 : ℝ) (19 / 300 : ℝ)
    (119407 / 20000 : ℝ) (923 / 600 : ℝ) (-71400 / 119407 : ℝ) (600 / 923 : ℝ) (600 / 923 : ℝ) (2233506940189 / 1250000000000 : ℝ) (17868055521521 / 10000000000000 : ℝ) (294464531309 / 2000000000000 : ℝ) (1472322661693 / 10000000000000 : ℝ)
    hlog_104 (by norm_num [quadLogLo, quadLogHi])

private lemma hqchain_106 :
    IntervalIntegrable (fun t => Real.log ((57311 / 5000 : ℝ) + (-357 / 100 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t)) volume (96559 / 71400 : ℝ) (961 / 600 : ℝ) ∧
      (385744883117 / 1250000000000 : ℝ) ≤ ∫ t in (96559 / 71400 : ℝ)..(961 / 600 : ℝ), Real.log ((57311 / 5000 : ℝ) + (-357 / 100 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (96559 / 71400 : ℝ)..(961 / 600 : ℝ), Real.log ((57311 / 5000 : ℝ) + (-357 / 100 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ≤ (617191815513 / 2000000000000 : ℝ) :=
  chain_int_bounds hqsub_103 hqsub_105 (by norm_num)

private lemma hqsub_107 :
    IntervalIntegrable (fun t => Real.log ((57311 / 5000 : ℝ) + (-357 / 100 : ℝ) * t) / ((223 / 50 : ℝ) + (-1 : ℝ) * t)) volume (96559 / 71400 : ℝ) (59 / 40 : ℝ) ∧
      (149633930083 / 2000000000000 : ℝ) ≤ ∫ t in (96559 / 71400 : ℝ)..(59 / 40 : ℝ), Real.log ((57311 / 5000 : ℝ) + (-357 / 100 : ℝ) * t) / ((223 / 50 : ℝ) + (-1 : ℝ) * t) ∧
      ∫ t in (96559 / 71400 : ℝ)..(59 / 40 : ℝ), Real.log ((57311 / 5000 : ℝ) + (-357 / 100 : ℝ) * t) / ((223 / 50 : ℝ) + (-1 : ℝ) * t) ≤ (748169651059 / 10000000000000 : ℝ) :=
  quad_log_div_sub (57311 / 5000 : ℝ) (-357 / 100 : ℝ) (223 / 50 : ℝ) (-1 : ℝ) (96559 / 71400 : ℝ) (59 / 40 : ℝ) (100937 / 71400 : ℝ) (2189 / 35700 : ℝ)
    (128307 / 20000 : ℝ) (217507 / 71400 : ℝ) (-23800 / 42769 : ℝ) (-71400 / 217507 : ℝ) (23800 / 42769 : ℝ) (290420868157 / 156250000000 : ℝ) (18586935562053 / 10000000000000 : ℝ) (149633930083 / 2000000000000 : ℝ) (748169651059 / 10000000000000 : ℝ)
    hlog_102 (by norm_num [quadLogLo, quadLogHi])

private lemma hqsub_108 :
    IntervalIntegrable (fun t => Real.log ((57311 / 5000 : ℝ) + (-357 / 100 : ℝ) * t) / ((223 / 50 : ℝ) + (-1 : ℝ) * t)) volume (59 / 40 : ℝ) (961 / 600 : ℝ) ∧
      (387277554029 / 5000000000000 : ℝ) ≤ ∫ t in (59 / 40 : ℝ)..(961 / 600 : ℝ), Real.log ((57311 / 5000 : ℝ) + (-357 / 100 : ℝ) * t) / ((223 / 50 : ℝ) + (-1 : ℝ) * t) ∧
      ∫ t in (59 / 40 : ℝ)..(961 / 600 : ℝ), Real.log ((57311 / 5000 : ℝ) + (-357 / 100 : ℝ) * t) / ((223 / 50 : ℝ) + (-1 : ℝ) * t) ≤ (774555109351 / 10000000000000 : ℝ) :=
  quad_log_div_sub (57311 / 5000 : ℝ) (-357 / 100 : ℝ) (223 / 50 : ℝ) (-1 : ℝ) (59 / 40 : ℝ) (961 / 600 : ℝ) (923 / 600 : ℝ) (19 / 300 : ℝ)
    (119407 / 20000 : ℝ) (1753 / 600 : ℝ) (-71400 / 119407 : ℝ) (-600 / 1753 : ℝ) (71400 / 119407 : ℝ) (2233506940189 / 1250000000000 : ℝ) (17868055521521 / 10000000000000 : ℝ) (387277554029 / 5000000000000 : ℝ) (774555109351 / 10000000000000 : ℝ)
    hlog_104 (by norm_num [quadLogLo, quadLogHi])

private lemma hqchain_109 :
    IntervalIntegrable (fun t => Real.log ((57311 / 5000 : ℝ) + (-357 / 100 : ℝ) * t) / ((223 / 50 : ℝ) + (-1 : ℝ) * t)) volume (96559 / 71400 : ℝ) (961 / 600 : ℝ) ∧
      (1522724758473 / 10000000000000 : ℝ) ≤ ∫ t in (96559 / 71400 : ℝ)..(961 / 600 : ℝ), Real.log ((57311 / 5000 : ℝ) + (-357 / 100 : ℝ) * t) / ((223 / 50 : ℝ) + (-1 : ℝ) * t) ∧
      ∫ t in (96559 / 71400 : ℝ)..(961 / 600 : ℝ), Real.log ((57311 / 5000 : ℝ) + (-357 / 100 : ℝ) * t) / ((223 / 50 : ℝ) + (-1 : ℝ) * t) ≤ (152272476041 / 1000000000000 : ℝ) :=
  chain_int_bounds hqsub_107 hqsub_108 (by norm_num)

private lemma hlog_110 : (1309657263901 / 1250000000000 : ℝ) ≤ Real.log (42411 / 14875 : ℝ) ∧ Real.log (42411 / 14875 : ℝ) ≤ (10477258111217 / 10000000000000 : ℝ) :=
  log_rat_bounds (42411 / 14875 : ℝ) (899 / 762499 : ℝ) (7) (-2) (-1) (1309657263901 / 1250000000000 : ℝ) (10477258111217 / 10000000000000 : ℝ)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hqsub_111 :
    IntervalIntegrable (fun t => Real.log ((1561 / 250 : ℝ) + (-12 / 5 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t)) volume (96559 / 71400 : ℝ) (59 / 40 : ℝ) ∧
      (113713208797 / 1250000000000 : ℝ) ≤ ∫ t in (96559 / 71400 : ℝ)..(59 / 40 : ℝ), Real.log ((1561 / 250 : ℝ) + (-12 / 5 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (96559 / 71400 : ℝ)..(59 / 40 : ℝ), Real.log ((1561 / 250 : ℝ) + (-12 / 5 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ≤ (909705687739 / 10000000000000 : ℝ) :=
  quad_log_div_sub (1561 / 250 : ℝ) (-12 / 5 : ℝ) (0 : ℝ) (1 : ℝ) (96559 / 71400 : ℝ) (59 / 40 : ℝ) (100937 / 71400 : ℝ) (2189 / 35700 : ℝ)
    (42411 / 14875 : ℝ) (100937 / 71400 : ℝ) (-11900 / 14137 : ℝ) (71400 / 100937 : ℝ) (11900 / 14137 : ℝ) (1309657263901 / 1250000000000 : ℝ) (10477258111217 / 10000000000000 : ℝ) (113713208797 / 1250000000000 : ℝ) (909705687739 / 10000000000000 : ℝ)
    hlog_110 (by norm_num [quadLogLo, quadLogHi])

private lemma hlog_112 : (9368773654821 / 10000000000000 : ℝ) ≤ Real.log (319 / 125 : ℝ) ∧ Real.log (319 / 125 : ℝ) ≤ (9368773654829 / 10000000000000 : ℝ) :=
  log_rat_bounds (319 / 125 : ℝ) (83 / 20333 : ℝ) (-5) (4) (0) (9368773654821 / 10000000000000 : ℝ) (9368773654829 / 10000000000000 : ℝ)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hqsub_113 :
    IntervalIntegrable (fun t => Real.log ((1561 / 250 : ℝ) + (-12 / 5 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t)) volume (59 / 40 : ℝ) (961 / 600 : ℝ) ∧
      (772049264889 / 10000000000000 : ℝ) ≤ ∫ t in (59 / 40 : ℝ)..(961 / 600 : ℝ), Real.log ((1561 / 250 : ℝ) + (-12 / 5 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (59 / 40 : ℝ)..(961 / 600 : ℝ), Real.log ((1561 / 250 : ℝ) + (-12 / 5 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ≤ (772049302249 / 10000000000000 : ℝ) :=
  quad_log_div_sub (1561 / 250 : ℝ) (-12 / 5 : ℝ) (0 : ℝ) (1 : ℝ) (59 / 40 : ℝ) (961 / 600 : ℝ) (923 / 600 : ℝ) (19 / 300 : ℝ)
    (319 / 125 : ℝ) (923 / 600 : ℝ) (-300 / 319 : ℝ) (600 / 923 : ℝ) (300 / 319 : ℝ) (9368773654821 / 10000000000000 : ℝ) (9368773654829 / 10000000000000 : ℝ) (772049264889 / 10000000000000 : ℝ) (772049302249 / 10000000000000 : ℝ)
    hlog_112 (by norm_num [quadLogLo, quadLogHi])

private lemma hqchain_114 :
    IntervalIntegrable (fun t => Real.log ((1561 / 250 : ℝ) + (-12 / 5 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t)) volume (96559 / 71400 : ℝ) (961 / 600 : ℝ) ∧
      (336350987053 / 2000000000000 : ℝ) ≤ ∫ t in (96559 / 71400 : ℝ)..(961 / 600 : ℝ), Real.log ((1561 / 250 : ℝ) + (-12 / 5 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (96559 / 71400 : ℝ)..(961 / 600 : ℝ), Real.log ((1561 / 250 : ℝ) + (-12 / 5 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ≤ (420438747497 / 2500000000000 : ℝ) :=
  chain_int_bounds hqsub_111 hqsub_113 (by norm_num)

private lemma hqsub_115 :
    IntervalIntegrable (fun t => Real.log ((1561 / 250 : ℝ) + (-12 / 5 : ℝ) * t) / ((223 / 50 : ℝ) + (-1 : ℝ) * t)) volume (96559 / 71400 : ℝ) (59 / 40 : ℝ) ∧
      (421512874391 / 10000000000000 : ℝ) ≤ ∫ t in (96559 / 71400 : ℝ)..(59 / 40 : ℝ), Real.log ((1561 / 250 : ℝ) + (-12 / 5 : ℝ) * t) / ((223 / 50 : ℝ) + (-1 : ℝ) * t) ∧
      ∫ t in (96559 / 71400 : ℝ)..(59 / 40 : ℝ), Real.log ((1561 / 250 : ℝ) + (-12 / 5 : ℝ) * t) / ((223 / 50 : ℝ) + (-1 : ℝ) * t) ≤ (52689110251 / 1250000000000 : ℝ) :=
  quad_log_div_sub (1561 / 250 : ℝ) (-12 / 5 : ℝ) (223 / 50 : ℝ) (-1 : ℝ) (96559 / 71400 : ℝ) (59 / 40 : ℝ) (100937 / 71400 : ℝ) (2189 / 35700 : ℝ)
    (42411 / 14875 : ℝ) (217507 / 71400 : ℝ) (-11900 / 14137 : ℝ) (-71400 / 217507 : ℝ) (11900 / 14137 : ℝ) (1309657263901 / 1250000000000 : ℝ) (10477258111217 / 10000000000000 : ℝ) (421512874391 / 10000000000000 : ℝ) (52689110251 / 1250000000000 : ℝ)
    hlog_110 (by norm_num [quadLogLo, quadLogHi])

private lemma hqsub_116 :
    IntervalIntegrable (fun t => Real.log ((1561 / 250 : ℝ) + (-12 / 5 : ℝ) * t) / ((223 / 50 : ℝ) + (-1 : ℝ) * t)) volume (59 / 40 : ℝ) (961 / 600 : ℝ) ∧
      (3170283861 / 78125000000 : ℝ) ≤ ∫ t in (59 / 40 : ℝ)..(961 / 600 : ℝ), Real.log ((1561 / 250 : ℝ) + (-12 / 5 : ℝ) * t) / ((223 / 50 : ℝ) + (-1 : ℝ) * t) ∧
      ∫ t in (59 / 40 : ℝ)..(961 / 600 : ℝ), Real.log ((1561 / 250 : ℝ) + (-12 / 5 : ℝ) * t) / ((223 / 50 : ℝ) + (-1 : ℝ) * t) ≤ (101449088393 / 2500000000000 : ℝ) :=
  quad_log_div_sub (1561 / 250 : ℝ) (-12 / 5 : ℝ) (223 / 50 : ℝ) (-1 : ℝ) (59 / 40 : ℝ) (961 / 600 : ℝ) (923 / 600 : ℝ) (19 / 300 : ℝ)
    (319 / 125 : ℝ) (1753 / 600 : ℝ) (-300 / 319 : ℝ) (-600 / 1753 : ℝ) (300 / 319 : ℝ) (9368773654821 / 10000000000000 : ℝ) (9368773654829 / 10000000000000 : ℝ) (3170283861 / 78125000000 : ℝ) (101449088393 / 2500000000000 : ℝ)
    hlog_112 (by norm_num [quadLogLo, quadLogHi])

private lemma hqchain_117 :
    IntervalIntegrable (fun t => Real.log ((1561 / 250 : ℝ) + (-12 / 5 : ℝ) * t) / ((223 / 50 : ℝ) + (-1 : ℝ) * t)) volume (96559 / 71400 : ℝ) (961 / 600 : ℝ) ∧
      (827309208599 / 10000000000000 : ℝ) ≤ ∫ t in (96559 / 71400 : ℝ)..(961 / 600 : ℝ), Real.log ((1561 / 250 : ℝ) + (-12 / 5 : ℝ) * t) / ((223 / 50 : ℝ) + (-1 : ℝ) * t) ∧
      ∫ t in (96559 / 71400 : ℝ)..(961 / 600 : ℝ), Real.log ((1561 / 250 : ℝ) + (-12 / 5 : ℝ) * t) / ((223 / 50 : ℝ) + (-1 : ℝ) * t) ≤ (41365461779 / 500000000000 : ℝ) :=
  chain_int_bounds hqsub_115 hqsub_116 (by norm_num)

private lemma hact_q6_118 :
    IntervalIntegrable (fun t => Real.log ((223 / 50 : ℝ) ^ (2 : ℕ) / (((357 / 100 : ℝ) * (223 / 50 : ℝ) - (223 / 50 : ℝ) - (357 / 100 : ℝ) * t) * ((12 / 5 : ℝ) * (223 / 50 : ℝ) - (223 / 50 : ℝ) - (12 / 5 : ℝ) * t))) / (5 * t * (1 - t / (223 / 50 : ℝ)))) volume (96559 / 71400 : ℝ) (961 / 600 : ℝ) ∧
      (44205478033 / 5000000000000 : ℝ) ≤ ∫ t in (96559 / 71400 : ℝ)..(961 / 600 : ℝ), Real.log ((223 / 50 : ℝ) ^ (2 : ℕ) / (((357 / 100 : ℝ) * (223 / 50 : ℝ) - (223 / 50 : ℝ) - (357 / 100 : ℝ) * t) * ((12 / 5 : ℝ) * (223 / 50 : ℝ) - (223 / 50 : ℝ) - (12 / 5 : ℝ) * t))) / (5 * t * (1 - t / (223 / 50 : ℝ))) :=
  active_q_6 (223 / 50 : ℝ) (357 / 100 : ℝ) (12 / 5 : ℝ) (57311 / 5000 : ℝ) (-357 / 100 : ℝ) (1561 / 250 : ℝ) (-12 / 5 : ℝ) (96559 / 71400 : ℝ) (961 / 600 : ℝ) (114359 / 96559 : ℝ) (44377 / 40817 : ℝ)
    (3737871915079 / 2500000000000 : ℝ) (7475743830161 / 5000000000000 : ℝ) (422971006547 / 2500000000000 : ℝ) (422971006549 / 2500000000000 : ℝ) (209056639767 / 2500000000000 : ℝ) (33449062363 / 400000000000 : ℝ)
    (385744883117 / 1250000000000 : ℝ) (617191815513 / 2000000000000 : ℝ) (1522724758473 / 10000000000000 : ℝ) (152272476041 / 1000000000000 : ℝ) (336350987053 / 2000000000000 : ℝ) (420438747497 / 2500000000000 : ℝ) (827309208599 / 10000000000000 : ℝ) (41365461779 / 500000000000 : ℝ) (44205478033 / 5000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog_99 hlog_100 hlog_101 hqchain_106 hqchain_109 hqchain_114 hqchain_117 (by norm_num)

private lemma hterm_98 :
    IntervalIntegrable (fun t => ind (96559 / 71400 : ℝ) (961 / 600 : ℝ) t / (5 * t * (1 - t / (223 / 50 : ℝ))) * Real.log ((223 / 50 : ℝ) ^ (2 : ℕ) / (((357 / 100 : ℝ) * (223 / 50 : ℝ) - (223 / 50 : ℝ) - (357 / 100 : ℝ) * t) * ((12 / 5 : ℝ) * (223 / 50 : ℝ) - (223 / 50 : ℝ) - (12 / 5 : ℝ) * t)))) volume (1 : ℝ) (11 / 5 : ℝ) ∧
      (44205478033 / 5000000000000 : ℝ) ≤ ∫ t in (1 : ℝ)..(11 / 5 : ℝ), ind (96559 / 71400 : ℝ) (961 / 600 : ℝ) t / (5 * t * (1 - t / (223 / 50 : ℝ))) * Real.log ((223 / 50 : ℝ) ^ (2 : ℕ) / (((357 / 100 : ℝ) * (223 / 50 : ℝ) - (223 / 50 : ℝ) - (357 / 100 : ℝ) * t) * ((12 / 5 : ℝ) * (223 / 50 : ℝ) - (223 / 50 : ℝ) - (12 / 5 : ℝ) * t))) :=
  bound_ind_div_active (1 : ℝ) (11 / 5 : ℝ) (96559 / 71400 : ℝ) (961 / 600 : ℝ) (96559 / 71400 : ℝ) (961 / 600 : ℝ) (44205478033 / 5000000000000 : ℝ)
    (fun t => 5 * t * (1 - t / (223 / 50 : ℝ))) (fun t => (223 / 50 : ℝ) ^ (2 : ℕ) / (((357 / 100 : ℝ) * (223 / 50 : ℝ) - (223 / 50 : ℝ) - (357 / 100 : ℝ) * t) * ((12 / 5 : ℝ) * (223 / 50 : ℝ) - (223 / 50 : ℝ) - (12 / 5 : ℝ) * t)))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (Or.inr rfl) (Or.inr rfl) hact_q6_118

private lemma hlog_120 : (337788809393 / 10000000000000 : ℝ) ≤ Real.log (4849804 / 4688719 : ℝ) ∧ Real.log (4849804 / 4688719 : ℝ) ≤ (337788809403 / 10000000000000 : ℝ) :=
  log_rat_bounds (4849804 / 4688719 : ℝ) (1517367 / 301595383 : ℝ) (7) (0) (-3) (337788809393 / 10000000000000 : ℝ) (337788809403 / 10000000000000 : ℝ)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hlog_121 : (194390237983 / 10000000000000 : ℝ) ≤ Real.log (1673497 / 1641280 : ℝ) ∧ Real.log (1673497 / 1641280 : ℝ) ≤ (24298779749 / 1250000000000 : ℝ) :=
  log_rat_bounds (1673497 / 1641280 : ℝ) (11701 / 3335293 : ℝ) (-4) (4) (-1) (194390237983 / 10000000000000 : ℝ) (24298779749 / 1250000000000 : ℝ)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hlog_122 : (3023819799471 / 5000000000000 : ℝ) ≤ Real.log (2143817 / 1170960 : ℝ) ∧ Real.log (2143817 / 1170960 : ℝ) ≤ (6047639598947 / 10000000000000 : ℝ) :=
  log_rat_bounds (2143817 / 1170960 : ℝ) (36089 / 4251545 : ℝ) (0) (2) (-1) (3023819799471 / 5000000000000 : ℝ) (6047639598947 / 10000000000000 : ℝ)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hqsub_123 :
    IntervalIntegrable (fun t => Real.log ((173 / 50 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t)) volume (961 / 600 : ℝ) (1212451 / 731850 : ℝ) ∧
      (204298361017 / 10000000000000 : ℝ) ≤ ∫ t in (961 / 600 : ℝ)..(1212451 / 731850 : ℝ), Real.log ((173 / 50 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (961 / 600 : ℝ)..(1212451 / 731850 : ℝ), Real.log ((173 / 50 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ≤ (204298361027 / 10000000000000 : ℝ) :=
  quad_log_div_sub (173 / 50 : ℝ) (-1 : ℝ) (0 : ℝ) (1 : ℝ) (961 / 600 : ℝ) (1212451 / 731850 : ℝ) (9538523 / 5854800 : ℝ) (10739 / 390320 : ℝ)
    (2143817 / 1170960 : ℝ) (9538523 / 5854800 : ℝ) (-1170960 / 2143817 : ℝ) (5854800 / 9538523 : ℝ) (5854800 / 9538523 : ℝ) (3023819799471 / 5000000000000 : ℝ) (6047639598947 / 10000000000000 : ℝ) (204298361017 / 10000000000000 : ℝ) (204298361027 / 10000000000000 : ℝ)
    hlog_122 (by norm_num [quadLogLo, quadLogHi])

private lemma hqsub_124 :
    IntervalIntegrable (fun t => Real.log ((173 / 50 : ℝ) + (-1 : ℝ) * t) / ((223 / 50 : ℝ) + (-1 : ℝ) * t)) volume (961 / 600 : ℝ) (1212451 / 731850 : ℝ) ∧
      (29385856963 / 2500000000000 : ℝ) ≤ ∫ t in (961 / 600 : ℝ)..(1212451 / 731850 : ℝ), Real.log ((173 / 50 : ℝ) + (-1 : ℝ) * t) / ((223 / 50 : ℝ) + (-1 : ℝ) * t) ∧
      ∫ t in (961 / 600 : ℝ)..(1212451 / 731850 : ℝ), Real.log ((173 / 50 : ℝ) + (-1 : ℝ) * t) / ((223 / 50 : ℝ) + (-1 : ℝ) * t) ≤ (23508685571 / 2000000000000 : ℝ) :=
  quad_log_div_sub (173 / 50 : ℝ) (-1 : ℝ) (223 / 50 : ℝ) (-1 : ℝ) (961 / 600 : ℝ) (1212451 / 731850 : ℝ) (9538523 / 5854800 : ℝ) (10739 / 390320 : ℝ)
    (2143817 / 1170960 : ℝ) (3314777 / 1170960 : ℝ) (-1170960 / 2143817 : ℝ) (-1170960 / 3314777 : ℝ) (1170960 / 2143817 : ℝ) (3023819799471 / 5000000000000 : ℝ) (6047639598947 / 10000000000000 : ℝ) (29385856963 / 2500000000000 : ℝ) (23508685571 / 2000000000000 : ℝ)
    hlog_122 (by norm_num [quadLogLo, quadLogHi])

private lemma hlog_125 : (8654760948621 / 5000000000000 : ℝ) ≤ Real.log (1851897 / 328000 : ℝ) ∧ Real.log (1851897 / 328000 : ℝ) ≤ (17309521897249 / 10000000000000 : ℝ) :=
  log_rat_bounds (1851897 / 328000 : ℝ) (2299 / 1232299 : ℝ) (-3) (2) (1) (8654760948621 / 5000000000000 : ℝ) (17309521897249 / 10000000000000 : ℝ)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hqsub_126 :
    IntervalIntegrable (fun t => Real.log ((57311 / 5000 : ℝ) + (-357 / 100 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t)) volume (961 / 600 : ℝ) (1212451 / 731850 : ℝ) ∧
      (146178080637 / 2500000000000 : ℝ) ≤ ∫ t in (961 / 600 : ℝ)..(1212451 / 731850 : ℝ), Real.log ((57311 / 5000 : ℝ) + (-357 / 100 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (961 / 600 : ℝ)..(1212451 / 731850 : ℝ), Real.log ((57311 / 5000 : ℝ) + (-357 / 100 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ≤ (584712322561 / 10000000000000 : ℝ) :=
  quad_log_div_sub (57311 / 5000 : ℝ) (-357 / 100 : ℝ) (0 : ℝ) (1 : ℝ) (961 / 600 : ℝ) (1212451 / 731850 : ℝ) (9538523 / 5854800 : ℝ) (10739 / 390320 : ℝ)
    (1851897 / 328000 : ℝ) (9538523 / 5854800 : ℝ) (-390320 / 617299 : ℝ) (5854800 / 9538523 : ℝ) (390320 / 617299 : ℝ) (8654760948621 / 5000000000000 : ℝ) (17309521897249 / 10000000000000 : ℝ) (146178080637 / 2500000000000 : ℝ) (584712322561 / 10000000000000 : ℝ)
    hlog_125 (by norm_num [quadLogLo, quadLogHi])

private lemma hqsub_127 :
    IntervalIntegrable (fun t => Real.log ((57311 / 5000 : ℝ) + (-357 / 100 : ℝ) * t) / ((223 / 50 : ℝ) + (-1 : ℝ) * t)) volume (961 / 600 : ℝ) (1212451 / 731850 : ℝ) ∧
      (168229722373 / 5000000000000 : ℝ) ≤ ∫ t in (961 / 600 : ℝ)..(1212451 / 731850 : ℝ), Real.log ((57311 / 5000 : ℝ) + (-357 / 100 : ℝ) * t) / ((223 / 50 : ℝ) + (-1 : ℝ) * t) ∧
      ∫ t in (961 / 600 : ℝ)..(1212451 / 731850 : ℝ), Real.log ((57311 / 5000 : ℝ) + (-357 / 100 : ℝ) * t) / ((223 / 50 : ℝ) + (-1 : ℝ) * t) ≤ (336459444753 / 10000000000000 : ℝ) :=
  quad_log_div_sub (57311 / 5000 : ℝ) (-357 / 100 : ℝ) (223 / 50 : ℝ) (-1 : ℝ) (961 / 600 : ℝ) (1212451 / 731850 : ℝ) (9538523 / 5854800 : ℝ) (10739 / 390320 : ℝ)
    (1851897 / 328000 : ℝ) (3314777 / 1170960 : ℝ) (-390320 / 617299 : ℝ) (-1170960 / 3314777 : ℝ) (390320 / 617299 : ℝ) (8654760948621 / 5000000000000 : ℝ) (17309521897249 / 10000000000000 : ℝ) (168229722373 / 5000000000000 : ℝ) (336459444753 / 10000000000000 : ℝ)
    hlog_125 (by norm_num [quadLogLo, quadLogHi])

private lemma hact_q7_128 :
    IntervalIntegrable (fun t => Real.log ((223 / 50 : ℝ) * ((223 / 50 : ℝ) - 1 - t) / ((357 / 100 : ℝ) * (223 / 50 : ℝ) - (223 / 50 : ℝ) - (357 / 100 : ℝ) * t)) / (5 * t * (1 - t / (223 / 50 : ℝ)))) volume (961 / 600 : ℝ) (1212451 / 731850 : ℝ) ∧
      (39271373509 / 10000000000000 : ℝ) ≤ ∫ t in (961 / 600 : ℝ)..(1212451 / 731850 : ℝ), Real.log ((223 / 50 : ℝ) * ((223 / 50 : ℝ) - 1 - t) / ((357 / 100 : ℝ) * (223 / 50 : ℝ) - (223 / 50 : ℝ) - (357 / 100 : ℝ) * t)) / (5 * t * (1 - t / (223 / 50 : ℝ))) :=
  active_q_7 (223 / 50 : ℝ) (357 / 100 : ℝ) (173 / 50 : ℝ) (57311 / 5000 : ℝ) (-357 / 100 : ℝ) (961 / 600 : ℝ) (1212451 / 731850 : ℝ) (4849804 / 4688719 : ℝ) (1673497 / 1641280 : ℝ)
    (3737871915079 / 2500000000000 : ℝ) (7475743830161 / 5000000000000 : ℝ) (337788809393 / 10000000000000 : ℝ) (337788809403 / 10000000000000 : ℝ) (194390237983 / 10000000000000 : ℝ) (24298779749 / 1250000000000 : ℝ)
    (204298361017 / 10000000000000 : ℝ) (204298361027 / 10000000000000 : ℝ) (29385856963 / 2500000000000 : ℝ) (23508685571 / 2000000000000 : ℝ) (146178080637 / 2500000000000 : ℝ) (584712322561 / 10000000000000 : ℝ) (168229722373 / 5000000000000 : ℝ) (336459444753 / 10000000000000 : ℝ) (39271373509 / 10000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog_99 hlog_120 hlog_121 hqsub_123 hqsub_124 hqsub_126 hqsub_127 (by norm_num)

private lemma hterm_119 :
    IntervalIntegrable (fun t => ind (961 / 600 : ℝ) (1212451 / 731850 : ℝ) t / (5 * t * (1 - t / (223 / 50 : ℝ))) * Real.log ((223 / 50 : ℝ) * ((223 / 50 : ℝ) - 1 - t) / ((357 / 100 : ℝ) * (223 / 50 : ℝ) - (223 / 50 : ℝ) - (357 / 100 : ℝ) * t))) volume (1 : ℝ) (11 / 5 : ℝ) ∧
      (39271373509 / 10000000000000 : ℝ) ≤ ∫ t in (1 : ℝ)..(11 / 5 : ℝ), ind (961 / 600 : ℝ) (1212451 / 731850 : ℝ) t / (5 * t * (1 - t / (223 / 50 : ℝ))) * Real.log ((223 / 50 : ℝ) * ((223 / 50 : ℝ) - 1 - t) / ((357 / 100 : ℝ) * (223 / 50 : ℝ) - (223 / 50 : ℝ) - (357 / 100 : ℝ) * t)) :=
  bound_ind_div_active (1 : ℝ) (11 / 5 : ℝ) (961 / 600 : ℝ) (1212451 / 731850 : ℝ) (961 / 600 : ℝ) (1212451 / 731850 : ℝ) (39271373509 / 10000000000000 : ℝ)
    (fun t => 5 * t * (1 - t / (223 / 50 : ℝ))) (fun t => (223 / 50 : ℝ) * ((223 / 50 : ℝ) - 1 - t) / ((357 / 100 : ℝ) * (223 / 50 : ℝ) - (223 / 50 : ℝ) - (357 / 100 : ℝ) * t))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (Or.inr rfl) (Or.inr rfl) hact_q7_128

private lemma hlog_130 : (508122414417 / 2500000000000 : ℝ) ≤ Real.log (5437 / 4437 : ℝ) ∧ Real.log (5437 / 4437 : ℝ) ≤ (254061207209 / 1250000000000 : ℝ) :=
  log_rat_bounds (5437 / 4437 : ℝ) (563 / 53807 : ℝ) (1) (1) (-1) (508122414417 / 2500000000000 : ℝ) (254061207209 / 1250000000000 : ℝ)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hlog_131 : (1031842362349 / 10000000000000 : ℝ) ≤ Real.log (51 / 46 : ℝ) ∧ Real.log (51 / 46 : ℝ) ≤ (257960590589 / 2500000000000 : ℝ) :=
  log_rat_bounds (51 / 46 : ℝ) (11 / 839 : ℝ) (0) (3) (-2) (1031842362349 / 10000000000000 : ℝ) (257960590589 / 2500000000000 : ℝ)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hlog_132 : (3611658750173 / 2500000000000 : ℝ) ≤ Real.log (169617 / 40000 : ℝ) ∧ Real.log (169617 / 40000 : ℝ) ≤ (144466350007 / 100000000000 : ℝ) :=
  log_rat_bounds (169617 / 40000 : ℝ) (289 / 112789 : ℝ) (-5) (3) (1) (3611658750173 / 2500000000000 : ℝ) (144466350007 / 100000000000 : ℝ)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hqsub_133 :
    IntervalIntegrable (fun t => Real.log ((41701 / 5000 : ℝ) + (-287 / 100 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t)) volume (19401 / 14350 : ℝ) (301 / 200 : ℝ) ∧
      (774727580031 / 5000000000000 : ℝ) ≤ ∫ t in (19401 / 14350 : ℝ)..(301 / 200 : ℝ), Real.log ((41701 / 5000 : ℝ) + (-287 / 100 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (19401 / 14350 : ℝ)..(301 / 200 : ℝ), Real.log ((41701 / 5000 : ℝ) + (-287 / 100 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ≤ (774727595571 / 5000000000000 : ℝ) :=
  quad_log_div_sub (41701 / 5000 : ℝ) (-287 / 100 : ℝ) (0 : ℝ) (1 : ℝ) (19401 / 14350 : ℝ) (301 / 200 : ℝ) (163991 / 114800 : ℝ) (8783 / 114800 : ℝ)
    (169617 / 40000 : ℝ) (163991 / 114800 : ℝ) (-400 / 591 : ℝ) (114800 / 163991 : ℝ) (114800 / 163991 : ℝ) (3611658750173 / 2500000000000 : ℝ) (144466350007 / 100000000000 : ℝ) (774727580031 / 5000000000000 : ℝ) (774727595571 / 5000000000000 : ℝ)
    hlog_132 (by norm_num [quadLogLo, quadLogHi])

private lemma hlog_134 : (3339587388191 / 2500000000000 : ℝ) ≤ Real.log (7758467 / 2040000 : ℝ) ∧ Real.log (7758467 / 2040000 : ℝ) ≤ (13358349552769 / 10000000000000 : ℝ) :=
  log_rat_bounds (7758467 / 2040000 : ℝ) (108467 / 15408467 : ℝ) (-2) (1) (1) (3339587388191 / 2500000000000 : ℝ) (13358349552769 / 10000000000000 : ℝ)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hqsub_135 :
    IntervalIntegrable (fun t => Real.log ((41701 / 5000 : ℝ) + (-287 / 100 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t)) volume (301 / 200 : ℝ) (1212451 / 731850 : ℝ) ∧
      (1283167114479 / 10000000000000 : ℝ) ≤ ∫ t in (301 / 200 : ℝ)..(1212451 / 731850 : ℝ), Real.log ((41701 / 5000 : ℝ) + (-287 / 100 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (301 / 200 : ℝ)..(1212451 / 731850 : ℝ), Real.log ((41701 / 5000 : ℝ) + (-287 / 100 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ≤ (1283167150699 / 10000000000000 : ℝ) :=
  quad_log_div_sub (41701 / 5000 : ℝ) (-287 / 100 : ℝ) (0 : ℝ) (1 : ℝ) (301 / 200 : ℝ) (1212451 / 731850 : ℝ) (9255541 / 5854800 : ℝ) (444067 / 5854800 : ℝ)
    (7758467 / 2040000 : ℝ) (9255541 / 5854800 : ℝ) (-5854800 / 7758467 : ℝ) (5854800 / 9255541 : ℝ) (5854800 / 7758467 : ℝ) (3339587388191 / 2500000000000 : ℝ) (13358349552769 / 10000000000000 : ℝ) (1283167114479 / 10000000000000 : ℝ) (1283167150699 / 10000000000000 : ℝ)
    hlog_134 (by norm_num [quadLogLo, quadLogHi])

private lemma hqchain_136 :
    IntervalIntegrable (fun t => Real.log ((41701 / 5000 : ℝ) + (-287 / 100 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t)) volume (19401 / 14350 : ℝ) (1212451 / 731850 : ℝ) ∧
      (2832622274541 / 10000000000000 : ℝ) ≤ ∫ t in (19401 / 14350 : ℝ)..(1212451 / 731850 : ℝ), Real.log ((41701 / 5000 : ℝ) + (-287 / 100 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (19401 / 14350 : ℝ)..(1212451 / 731850 : ℝ), Real.log ((41701 / 5000 : ℝ) + (-287 / 100 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ≤ (2832622341841 / 10000000000000 : ℝ) :=
  chain_int_bounds hqsub_133 hqsub_135 (by norm_num)

private lemma hqsub_137 :
    IntervalIntegrable (fun t => Real.log ((41701 / 5000 : ℝ) + (-287 / 100 : ℝ) * t) / ((223 / 50 : ℝ) + (-1 : ℝ) * t)) volume (19401 / 14350 : ℝ) (301 / 200 : ℝ) ∧
      (29155852083 / 400000000000 : ℝ) ≤ ∫ t in (19401 / 14350 : ℝ)..(301 / 200 : ℝ), Real.log ((41701 / 5000 : ℝ) + (-287 / 100 : ℝ) * t) / ((223 / 50 : ℝ) + (-1 : ℝ) * t) ∧
      ∫ t in (19401 / 14350 : ℝ)..(301 / 200 : ℝ), Real.log ((41701 / 5000 : ℝ) + (-287 / 100 : ℝ) * t) / ((223 / 50 : ℝ) + (-1 : ℝ) * t) ≤ (182224077959 / 2500000000000 : ℝ) :=
  quad_log_div_sub (41701 / 5000 : ℝ) (-287 / 100 : ℝ) (223 / 50 : ℝ) (-1 : ℝ) (19401 / 14350 : ℝ) (301 / 200 : ℝ) (163991 / 114800 : ℝ) (8783 / 114800 : ℝ)
    (169617 / 40000 : ℝ) (348017 / 114800 : ℝ) (-400 / 591 : ℝ) (-114800 / 348017 : ℝ) (400 / 591 : ℝ) (3611658750173 / 2500000000000 : ℝ) (144466350007 / 100000000000 : ℝ) (29155852083 / 400000000000 : ℝ) (182224077959 / 2500000000000 : ℝ)
    hlog_132 (by norm_num [quadLogLo, quadLogHi])

private lemma hqsub_138 :
    IntervalIntegrable (fun t => Real.log ((41701 / 5000 : ℝ) + (-287 / 100 : ℝ) * t) / ((223 / 50 : ℝ) + (-1 : ℝ) * t)) volume (301 / 200 : ℝ) (1212451 / 731850 : ℝ) ∧
      (703418095727 / 10000000000000 : ℝ) ≤ ∫ t in (301 / 200 : ℝ)..(1212451 / 731850 : ℝ), Real.log ((41701 / 5000 : ℝ) + (-287 / 100 : ℝ) * t) / ((223 / 50 : ℝ) + (-1 : ℝ) * t) ∧
      ∫ t in (301 / 200 : ℝ)..(1212451 / 731850 : ℝ), Real.log ((41701 / 5000 : ℝ) + (-287 / 100 : ℝ) * t) / ((223 / 50 : ℝ) + (-1 : ℝ) * t) ≤ (70341811429 / 1000000000000 : ℝ) :=
  quad_log_div_sub (41701 / 5000 : ℝ) (-287 / 100 : ℝ) (223 / 50 : ℝ) (-1 : ℝ) (301 / 200 : ℝ) (1212451 / 731850 : ℝ) (9255541 / 5854800 : ℝ) (444067 / 5854800 : ℝ)
    (7758467 / 2040000 : ℝ) (16856867 / 5854800 : ℝ) (-5854800 / 7758467 : ℝ) (-5854800 / 16856867 : ℝ) (5854800 / 7758467 : ℝ) (3339587388191 / 2500000000000 : ℝ) (13358349552769 / 10000000000000 : ℝ) (703418095727 / 10000000000000 : ℝ) (70341811429 / 1000000000000 : ℝ)
    hlog_134 (by norm_num [quadLogLo, quadLogHi])

private lemma hqchain_139 :
    IntervalIntegrable (fun t => Real.log ((41701 / 5000 : ℝ) + (-287 / 100 : ℝ) * t) / ((223 / 50 : ℝ) + (-1 : ℝ) * t)) volume (19401 / 14350 : ℝ) (1212451 / 731850 : ℝ) ∧
      (716157198901 / 5000000000000 : ℝ) ≤ ∫ t in (19401 / 14350 : ℝ)..(1212451 / 731850 : ℝ), Real.log ((41701 / 5000 : ℝ) + (-287 / 100 : ℝ) * t) / ((223 / 50 : ℝ) + (-1 : ℝ) * t) ∧
      ∫ t in (19401 / 14350 : ℝ)..(1212451 / 731850 : ℝ), Real.log ((41701 / 5000 : ℝ) + (-287 / 100 : ℝ) * t) / ((223 / 50 : ℝ) + (-1 : ℝ) * t) ≤ (716157213063 / 5000000000000 : ℝ) :=
  chain_int_bounds hqsub_137 hqsub_138 (by norm_num)

private lemma hact_q8_140 :
    IntervalIntegrable (fun t => Real.log ((223 / 50 : ℝ) / ((287 / 100 : ℝ) * (223 / 50 : ℝ) - (223 / 50 : ℝ) - (287 / 100 : ℝ) * t)) / (5 * t * (1 - t / (223 / 50 : ℝ)))) volume (19401 / 14350 : ℝ) (1212451 / 731850 : ℝ) ∧
      (31669547047 / 5000000000000 : ℝ) ≤ ∫ t in (19401 / 14350 : ℝ)..(1212451 / 731850 : ℝ), Real.log ((223 / 50 : ℝ) / ((287 / 100 : ℝ) * (223 / 50 : ℝ) - (223 / 50 : ℝ) - (287 / 100 : ℝ) * t)) / (5 * t * (1 - t / (223 / 50 : ℝ))) :=
  active_q_8 (223 / 50 : ℝ) (287 / 100 : ℝ) (41701 / 5000 : ℝ) (-287 / 100 : ℝ) (19401 / 14350 : ℝ) (1212451 / 731850 : ℝ) (5437 / 4437 : ℝ) (51 / 46 : ℝ)
    (3737871915079 / 2500000000000 : ℝ) (7475743830161 / 5000000000000 : ℝ) (508122414417 / 2500000000000 : ℝ) (254061207209 / 1250000000000 : ℝ) (1031842362349 / 10000000000000 : ℝ) (257960590589 / 2500000000000 : ℝ)
    (2832622274541 / 10000000000000 : ℝ) (2832622341841 / 10000000000000 : ℝ) (716157198901 / 5000000000000 : ℝ) (716157213063 / 5000000000000 : ℝ) (31669547047 / 5000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlog_99 hlog_130 hlog_131 hqchain_136 hqchain_139 (by norm_num)

private lemma hterm_129 :
    IntervalIntegrable (fun t => ind (19401 / 14350 : ℝ) (1212451 / 731850 : ℝ) t / (5 * t * (1 - t / (223 / 50 : ℝ))) * Real.log ((223 / 50 : ℝ) / ((287 / 100 : ℝ) * (223 / 50 : ℝ) - (223 / 50 : ℝ) - (287 / 100 : ℝ) * t))) volume (1 : ℝ) (11 / 5 : ℝ) ∧
      (31669547047 / 5000000000000 : ℝ) ≤ ∫ t in (1 : ℝ)..(11 / 5 : ℝ), ind (19401 / 14350 : ℝ) (1212451 / 731850 : ℝ) t / (5 * t * (1 - t / (223 / 50 : ℝ))) * Real.log ((223 / 50 : ℝ) / ((287 / 100 : ℝ) * (223 / 50 : ℝ) - (223 / 50 : ℝ) - (287 / 100 : ℝ) * t)) :=
  bound_ind_div_active (1 : ℝ) (11 / 5 : ℝ) (19401 / 14350 : ℝ) (1212451 / 731850 : ℝ) (19401 / 14350 : ℝ) (1212451 / 731850 : ℝ) (31669547047 / 5000000000000 : ℝ)
    (fun t => 5 * t * (1 - t / (223 / 50 : ℝ))) (fun t => (223 / 50 : ℝ) / ((287 / 100 : ℝ) * (223 / 50 : ℝ) - (223 / 50 : ℝ) - (287 / 100 : ℝ) * t))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (Or.inr rfl) (Or.inr rfl) hact_q8_140

private lemma hlog_142 : (5374597713893 / 10000000000000 : ℝ) ≤ Real.log (2505347 / 1463700 : ℝ) ∧ Real.log (2505347 / 1463700 : ℝ) ≤ (2687298856951 / 5000000000000 : ℝ) :=
  log_rat_bounds (2505347 / 1463700 : ℝ) (7299 / 5003395 : ℝ) (7) (-1) (-2) (5374597713893 / 10000000000000 : ℝ) (2687298856951 / 5000000000000 : ℝ)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hqsub_143 :
    IntervalIntegrable (fun t => Real.log ((173 / 50 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t)) volume (1212451 / 731850 : ℝ) (46 / 25 : ℝ) ∧
      (564501603539 / 10000000000000 : ℝ) ≤ ∫ t in (1212451 / 731850 : ℝ)..(46 / 25 : ℝ), Real.log ((173 / 50 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (1212451 / 731850 : ℝ)..(46 / 25 : ℝ), Real.log ((173 / 50 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ≤ (564501630111 / 10000000000000 : ℝ) :=
  quad_log_div_sub (173 / 50 : ℝ) (-1 : ℝ) (0 : ℝ) (1 : ℝ) (1212451 / 731850 : ℝ) (46 / 25 : ℝ) (511811 / 292740 : ℝ) (134153 / 1463700 : ℝ)
    (2505347 / 1463700 : ℝ) (511811 / 292740 : ℝ) (-1463700 / 2505347 : ℝ) (292740 / 511811 : ℝ) (1463700 / 2505347 : ℝ) (5374597713893 / 10000000000000 : ℝ) (2687298856951 / 5000000000000 : ℝ) (564501603539 / 10000000000000 : ℝ) (564501630111 / 10000000000000 : ℝ)
    hlog_142 (by norm_num [quadLogLo, quadLogHi])

private lemma hlog_144 : (2126338677021 / 5000000000000 : ℝ) ≤ Real.log (153 / 100 : ℝ) ∧ Real.log (153 / 100 : ℝ) ≤ (850535470809 / 2000000000000 : ℝ) :=
  log_rat_bounds (153 / 100 : ℝ) (1 / 101 : ℝ) (-1) (1) (0) (2126338677021 / 5000000000000 : ℝ) (850535470809 / 2000000000000 : ℝ)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hqsub_145 :
    IntervalIntegrable (fun t => Real.log ((173 / 50 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t)) volume (46 / 25 : ℝ) (101 / 50 : ℝ) ∧
      (3177807681 / 80000000000 : ℝ) ≤ ∫ t in (46 / 25 : ℝ)..(101 / 50 : ℝ), Real.log ((173 / 50 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (46 / 25 : ℝ)..(101 / 50 : ℝ), Real.log ((173 / 50 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ≤ (397225999413 / 10000000000000 : ℝ) :=
  quad_log_div_sub (173 / 50 : ℝ) (-1 : ℝ) (0 : ℝ) (1 : ℝ) (46 / 25 : ℝ) (101 / 50 : ℝ) (193 / 100 : ℝ) (9 / 100 : ℝ)
    (153 / 100 : ℝ) (193 / 100 : ℝ) (-100 / 153 : ℝ) (100 / 193 : ℝ) (100 / 153 : ℝ) (2126338677021 / 5000000000000 : ℝ) (850535470809 / 2000000000000 : ℝ) (3177807681 / 80000000000 : ℝ) (397225999413 / 10000000000000 : ℝ)
    hlog_144 (by norm_num [quadLogLo, quadLogHi])

private lemma hlog_146 : (6002091849 / 20000000000 : ℝ) ≤ Real.log (27 / 20 : ℝ) ∧ Real.log (27 / 20 : ℝ) ≤ (3001045924507 / 10000000000000 : ℝ) :=
  log_rat_bounds (27 / 20 : ℝ) (0 : ℝ) (-2) (3) (-1) (6002091849 / 20000000000 : ℝ) (3001045924507 / 10000000000000 : ℝ)
    (by norm_num [LOG2_LO, LOG2_HI, LOG3_LO, LOG3_HI, LOG5_LO, LOG5_HI])

private lemma hqsub_147 :
    IntervalIntegrable (fun t => Real.log ((173 / 50 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t)) volume (101 / 50 : ℝ) (11 / 5 : ℝ) ∧
      (256345553883 / 10000000000000 : ℝ) ≤ ∫ t in (101 / 50 : ℝ)..(11 / 5 : ℝ), Real.log ((173 / 50 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (101 / 50 : ℝ)..(11 / 5 : ℝ), Real.log ((173 / 50 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ≤ (128172814511 / 5000000000000 : ℝ) :=
  quad_log_div_sub (173 / 50 : ℝ) (-1 : ℝ) (0 : ℝ) (1 : ℝ) (101 / 50 : ℝ) (11 / 5 : ℝ) (211 / 100 : ℝ) (9 / 100 : ℝ)
    (27 / 20 : ℝ) (211 / 100 : ℝ) (-20 / 27 : ℝ) (100 / 211 : ℝ) (20 / 27 : ℝ) (6002091849 / 20000000000 : ℝ) (3001045924507 / 10000000000000 : ℝ) (256345553883 / 10000000000000 : ℝ) (128172814511 / 5000000000000 : ℝ)
    hlog_146 (by norm_num [quadLogLo, quadLogHi])

private lemma hqchain_148 :
    IntervalIntegrable (fun t => Real.log ((173 / 50 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t)) volume (1212451 / 731850 : ℝ) (101 / 50 : ℝ) ∧
      (60107972729 / 625000000000 : ℝ) ≤ ∫ t in (1212451 / 731850 : ℝ)..(101 / 50 : ℝ), Real.log ((173 / 50 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (1212451 / 731850 : ℝ)..(101 / 50 : ℝ), Real.log ((173 / 50 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ≤ (240431907381 / 2500000000000 : ℝ) :=
  chain_int_bounds hqsub_143 hqsub_145 (by norm_num)

private lemma hqchain_149 :
    IntervalIntegrable (fun t => Real.log ((173 / 50 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t)) volume (1212451 / 731850 : ℝ) (11 / 5 : ℝ) ∧
      (1218073117547 / 10000000000000 : ℝ) ≤ ∫ t in (1212451 / 731850 : ℝ)..(11 / 5 : ℝ), Real.log ((173 / 50 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ∧
      ∫ t in (1212451 / 731850 : ℝ)..(11 / 5 : ℝ), Real.log ((173 / 50 : ℝ) + (-1 : ℝ) * t) / ((0 : ℝ) + (1 : ℝ) * t) ≤ (609036629273 / 5000000000000 : ℝ) :=
  chain_int_bounds hqchain_148 hqsub_147 (by norm_num)

private lemma hqsub_150 :
    IntervalIntegrable (fun t => Real.log ((173 / 50 : ℝ) + (-1 : ℝ) * t) / ((223 / 50 : ℝ) + (-1 : ℝ) * t)) volume (1212451 / 731850 : ℝ) (46 / 25 : ℝ) ∧
      (362727237471 / 10000000000000 : ℝ) ≤ ∫ t in (1212451 / 731850 : ℝ)..(46 / 25 : ℝ), Real.log ((173 / 50 : ℝ) + (-1 : ℝ) * t) / ((223 / 50 : ℝ) + (-1 : ℝ) * t) ∧
      ∫ t in (1212451 / 731850 : ℝ)..(46 / 25 : ℝ), Real.log ((173 / 50 : ℝ) + (-1 : ℝ) * t) / ((223 / 50 : ℝ) + (-1 : ℝ) * t) ≤ (362727253493 / 10000000000000 : ℝ) :=
  quad_log_div_sub (173 / 50 : ℝ) (-1 : ℝ) (223 / 50 : ℝ) (-1 : ℝ) (1212451 / 731850 : ℝ) (46 / 25 : ℝ) (511811 / 292740 : ℝ) (134153 / 1463700 : ℝ)
    (2505347 / 1463700 : ℝ) (3969047 / 1463700 : ℝ) (-1463700 / 2505347 : ℝ) (-1463700 / 3969047 : ℝ) (1463700 / 2505347 : ℝ) (5374597713893 / 10000000000000 : ℝ) (2687298856951 / 5000000000000 : ℝ) (362727237471 / 10000000000000 : ℝ) (362727253493 / 10000000000000 : ℝ)
    hlog_142 (by norm_num [quadLogLo, quadLogHi])

private lemma hqsub_151 :
    IntervalIntegrable (fun t => Real.log ((173 / 50 : ℝ) + (-1 : ℝ) * t) / ((223 / 50 : ℝ) + (-1 : ℝ) * t)) volume (46 / 25 : ℝ) (101 / 50 : ℝ) ∧
      (301781720053 / 10000000000000 : ℝ) ≤ ∫ t in (46 / 25 : ℝ)..(101 / 50 : ℝ), Real.log ((173 / 50 : ℝ) + (-1 : ℝ) * t) / ((223 / 50 : ℝ) + (-1 : ℝ) * t) ∧
      ∫ t in (46 / 25 : ℝ)..(101 / 50 : ℝ), Real.log ((173 / 50 : ℝ) + (-1 : ℝ) * t) / ((223 / 50 : ℝ) + (-1 : ℝ) * t) ≤ (301781749627 / 10000000000000 : ℝ) :=
  quad_log_div_sub (173 / 50 : ℝ) (-1 : ℝ) (223 / 50 : ℝ) (-1 : ℝ) (46 / 25 : ℝ) (101 / 50 : ℝ) (193 / 100 : ℝ) (9 / 100 : ℝ)
    (153 / 100 : ℝ) (253 / 100 : ℝ) (-100 / 153 : ℝ) (-100 / 253 : ℝ) (100 / 153 : ℝ) (2126338677021 / 5000000000000 : ℝ) (850535470809 / 2000000000000 : ℝ) (301781720053 / 10000000000000 : ℝ) (301781749627 / 10000000000000 : ℝ)
    hlog_144 (by norm_num [quadLogLo, quadLogHi])

private lemma hqsub_152 :
    IntervalIntegrable (fun t => Real.log ((173 / 50 : ℝ) + (-1 : ℝ) * t) / ((223 / 50 : ℝ) + (-1 : ℝ) * t)) volume (101 / 50 : ℝ) (11 / 5 : ℝ) ∧
      (228758133403 / 10000000000000 : ℝ) ≤ ∫ t in (101 / 50 : ℝ)..(11 / 5 : ℝ), Real.log ((173 / 50 : ℝ) + (-1 : ℝ) * t) / ((223 / 50 : ℝ) + (-1 : ℝ) * t) ∧
      ∫ t in (101 / 50 : ℝ)..(11 / 5 : ℝ), Real.log ((173 / 50 : ℝ) + (-1 : ℝ) * t) / ((223 / 50 : ℝ) + (-1 : ℝ) * t) ≤ (57189550191 / 2500000000000 : ℝ) :=
  quad_log_div_sub (173 / 50 : ℝ) (-1 : ℝ) (223 / 50 : ℝ) (-1 : ℝ) (101 / 50 : ℝ) (11 / 5 : ℝ) (211 / 100 : ℝ) (9 / 100 : ℝ)
    (27 / 20 : ℝ) (47 / 20 : ℝ) (-20 / 27 : ℝ) (-20 / 47 : ℝ) (20 / 27 : ℝ) (6002091849 / 20000000000 : ℝ) (3001045924507 / 10000000000000 : ℝ) (228758133403 / 10000000000000 : ℝ) (57189550191 / 2500000000000 : ℝ)
    hlog_146 (by norm_num [quadLogLo, quadLogHi])

private lemma hqchain_153 :
    IntervalIntegrable (fun t => Real.log ((173 / 50 : ℝ) + (-1 : ℝ) * t) / ((223 / 50 : ℝ) + (-1 : ℝ) * t)) volume (1212451 / 731850 : ℝ) (101 / 50 : ℝ) ∧
      (166127239381 / 2500000000000 : ℝ) ≤ ∫ t in (1212451 / 731850 : ℝ)..(101 / 50 : ℝ), Real.log ((173 / 50 : ℝ) + (-1 : ℝ) * t) / ((223 / 50 : ℝ) + (-1 : ℝ) * t) ∧
      ∫ t in (1212451 / 731850 : ℝ)..(101 / 50 : ℝ), Real.log ((173 / 50 : ℝ) + (-1 : ℝ) * t) / ((223 / 50 : ℝ) + (-1 : ℝ) * t) ≤ (8306362539 / 125000000000 : ℝ) :=
  chain_int_bounds hqsub_150 hqsub_151 (by norm_num)

private lemma hqchain_154 :
    IntervalIntegrable (fun t => Real.log ((173 / 50 : ℝ) + (-1 : ℝ) * t) / ((223 / 50 : ℝ) + (-1 : ℝ) * t)) volume (1212451 / 731850 : ℝ) (11 / 5 : ℝ) ∧
      (893267090927 / 10000000000000 : ℝ) ≤ ∫ t in (1212451 / 731850 : ℝ)..(11 / 5 : ℝ), Real.log ((173 / 50 : ℝ) + (-1 : ℝ) * t) / ((223 / 50 : ℝ) + (-1 : ℝ) * t) ∧
      ∫ t in (1212451 / 731850 : ℝ)..(11 / 5 : ℝ), Real.log ((173 / 50 : ℝ) + (-1 : ℝ) * t) / ((223 / 50 : ℝ) + (-1 : ℝ) * t) ≤ (223316800971 / 2500000000000 : ℝ) :=
  chain_int_bounds hqchain_153 hqsub_152 (by norm_num)

private lemma hact_q9_155 :
    IntervalIntegrable (fun t => Real.log ((223 / 50 : ℝ) - 1 - t) / (5 * t * (1 - t / (223 / 50 : ℝ)))) volume (1212451 / 731850 : ℝ) (11 / 5 : ℝ) ∧
      (211134020847 / 5000000000000 : ℝ) ≤ ∫ t in (1212451 / 731850 : ℝ)..(11 / 5 : ℝ), Real.log ((223 / 50 : ℝ) - 1 - t) / (5 * t * (1 - t / (223 / 50 : ℝ))) :=
  active_q_9 (223 / 50 : ℝ) (173 / 50 : ℝ) (1212451 / 731850 : ℝ) (11 / 5 : ℝ)
    (1218073117547 / 10000000000000 : ℝ) (609036629273 / 5000000000000 : ℝ) (893267090927 / 10000000000000 : ℝ) (223316800971 / 2500000000000 : ℝ) (211134020847 / 5000000000000 : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hqchain_149 hqchain_154 (by norm_num)

private lemma hterm_141 :
    IntervalIntegrable (fun t => ind (1212451 / 731850 : ℝ) (123 / 50 : ℝ) t / (5 * t * (1 - t / (223 / 50 : ℝ))) * Real.log ((223 / 50 : ℝ) - 1 - t)) volume (1 : ℝ) (11 / 5 : ℝ) ∧
      (211134020847 / 5000000000000 : ℝ) ≤ ∫ t in (1 : ℝ)..(11 / 5 : ℝ), ind (1212451 / 731850 : ℝ) (123 / 50 : ℝ) t / (5 * t * (1 - t / (223 / 50 : ℝ))) * Real.log ((223 / 50 : ℝ) - 1 - t) :=
  bound_ind_div_active (1 : ℝ) (11 / 5 : ℝ) (1212451 / 731850 : ℝ) (123 / 50 : ℝ) (1212451 / 731850 : ℝ) (11 / 5 : ℝ) (211134020847 / 5000000000000 : ℝ)
    (fun t => 5 * t * (1 - t / (223 / 50 : ℝ))) (fun t => (223 / 50 : ℝ) - 1 - t)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (Or.inr rfl) (Or.inl rfl) hact_q9_155

private lemma hsum_all_156 :
    IntervalIntegrable (fun t => (((((((((sigma0 t / ((5 : ℝ) * t) * Real.log (12800000000 / 407396143 : ℝ)) + (ind (123 / 50 : ℝ) (3 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) ^ (5 : ℕ) / (407396143 / 12500000 : ℝ)))) + (ind (5437 / 4100 : ℝ) (157 / 100 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) / ((187 / 100 : ℝ) * ((257 / 100 : ℝ) - t))))) + (ind (961 / 600 : ℝ) (123 / 50 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) / ((7 / 5 : ℝ) * ((173 / 50 : ℝ) - t))))) + (ind (961 / 600 : ℝ) (123 / 50 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) / ((7 / 5 : ℝ) * ((173 / 50 : ℝ) - t))))) + (ind (157 / 100 : ℝ) (123 / 50 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) ^ (2 : ℕ) / (48059 / 10000 : ℝ)))) + (ind (96559 / 71400 : ℝ) (961 / 600 : ℝ) t / (5 * t * (1 - t / (223 / 50 : ℝ))) * Real.log ((223 / 50 : ℝ) ^ (2 : ℕ) / (((357 / 100 : ℝ) * (223 / 50 : ℝ) - (223 / 50 : ℝ) - (357 / 100 : ℝ) * t) * ((12 / 5 : ℝ) * (223 / 50 : ℝ) - (223 / 50 : ℝ) - (12 / 5 : ℝ) * t))))) + (ind (961 / 600 : ℝ) (1212451 / 731850 : ℝ) t / (5 * t * (1 - t / (223 / 50 : ℝ))) * Real.log ((223 / 50 : ℝ) * ((223 / 50 : ℝ) - 1 - t) / ((357 / 100 : ℝ) * (223 / 50 : ℝ) - (223 / 50 : ℝ) - (357 / 100 : ℝ) * t)))) + (ind (19401 / 14350 : ℝ) (1212451 / 731850 : ℝ) t / (5 * t * (1 - t / (223 / 50 : ℝ))) * Real.log ((223 / 50 : ℝ) / ((287 / 100 : ℝ) * (223 / 50 : ℝ) - (223 / 50 : ℝ) - (287 / 100 : ℝ) * t)))) + (ind (1212451 / 731850 : ℝ) (123 / 50 : ℝ) t / (5 * t * (1 - t / (223 / 50 : ℝ))) * Real.log ((223 / 50 : ℝ) - 1 - t))) volume (1 : ℝ) (11 / 5 : ℝ) ∧
      (190649886673 / 1250000000000 : ℝ) ≤ ∫ t in (1 : ℝ)..(11 / 5 : ℝ), ((((((((((sigma0 t / ((5 : ℝ) * t) * Real.log (12800000000 / 407396143 : ℝ)) + (ind (123 / 50 : ℝ) (3 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) ^ (5 : ℕ) / (407396143 / 12500000 : ℝ)))) + (ind (5437 / 4100 : ℝ) (157 / 100 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) / ((187 / 100 : ℝ) * ((257 / 100 : ℝ) - t))))) + (ind (961 / 600 : ℝ) (123 / 50 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) / ((7 / 5 : ℝ) * ((173 / 50 : ℝ) - t))))) + (ind (961 / 600 : ℝ) (123 / 50 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) / ((7 / 5 : ℝ) * ((173 / 50 : ℝ) - t))))) + (ind (157 / 100 : ℝ) (123 / 50 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) ^ (2 : ℕ) / (48059 / 10000 : ℝ)))) + (ind (96559 / 71400 : ℝ) (961 / 600 : ℝ) t / (5 * t * (1 - t / (223 / 50 : ℝ))) * Real.log ((223 / 50 : ℝ) ^ (2 : ℕ) / (((357 / 100 : ℝ) * (223 / 50 : ℝ) - (223 / 50 : ℝ) - (357 / 100 : ℝ) * t) * ((12 / 5 : ℝ) * (223 / 50 : ℝ) - (223 / 50 : ℝ) - (12 / 5 : ℝ) * t))))) + (ind (961 / 600 : ℝ) (1212451 / 731850 : ℝ) t / (5 * t * (1 - t / (223 / 50 : ℝ))) * Real.log ((223 / 50 : ℝ) * ((223 / 50 : ℝ) - 1 - t) / ((357 / 100 : ℝ) * (223 / 50 : ℝ) - (223 / 50 : ℝ) - (357 / 100 : ℝ) * t)))) + (ind (19401 / 14350 : ℝ) (1212451 / 731850 : ℝ) t / (5 * t * (1 - t / (223 / 50 : ℝ))) * Real.log ((223 / 50 : ℝ) / ((287 / 100 : ℝ) * (223 / 50 : ℝ) - (223 / 50 : ℝ) - (287 / 100 : ℝ) * t)))) + (ind (1212451 / 731850 : ℝ) (123 / 50 : ℝ) t / (5 * t * (1 - t / (223 / 50 : ℝ))) * Real.log ((223 / 50 : ℝ) - 1 - t))) :=
  add10_int_lb hterm_s0_46 hterm_47 hterm_48 hterm_62 hterm_83 hterm_85 hterm_98 hterm_119 hterm_129 hterm_141 (by norm_num)


private lemma hkern_eq (t : ℝ) : tableKernel 2 t = ((((((((((sigma0 t / ((5 : ℝ) * t) * Real.log (12800000000 / 407396143 : ℝ)) + (ind (123 / 50 : ℝ) (3 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) ^ (5 : ℕ) / (407396143 / 12500000 : ℝ)))) + (ind (5437 / 4100 : ℝ) (157 / 100 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) / ((187 / 100 : ℝ) * ((257 / 100 : ℝ) - t))))) + (ind (961 / 600 : ℝ) (123 / 50 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) / ((7 / 5 : ℝ) * ((173 / 50 : ℝ) - t))))) + (ind (961 / 600 : ℝ) (123 / 50 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) / ((7 / 5 : ℝ) * ((173 / 50 : ℝ) - t))))) + (ind (157 / 100 : ℝ) (123 / 50 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) ^ (2 : ℕ) / (48059 / 10000 : ℝ)))) + (ind (96559 / 71400 : ℝ) (961 / 600 : ℝ) t / (5 * t * (1 - t / (223 / 50 : ℝ))) * Real.log ((223 / 50 : ℝ) ^ (2 : ℕ) / (((357 / 100 : ℝ) * (223 / 50 : ℝ) - (223 / 50 : ℝ) - (357 / 100 : ℝ) * t) * ((12 / 5 : ℝ) * (223 / 50 : ℝ) - (223 / 50 : ℝ) - (12 / 5 : ℝ) * t))))) + (ind (961 / 600 : ℝ) (1212451 / 731850 : ℝ) t / (5 * t * (1 - t / (223 / 50 : ℝ))) * Real.log ((223 / 50 : ℝ) * ((223 / 50 : ℝ) - 1 - t) / ((357 / 100 : ℝ) * (223 / 50 : ℝ) - (223 / 50 : ℝ) - (357 / 100 : ℝ) * t)))) + (ind (19401 / 14350 : ℝ) (1212451 / 731850 : ℝ) t / (5 * t * (1 - t / (223 / 50 : ℝ))) * Real.log ((223 / 50 : ℝ) / ((287 / 100 : ℝ) * (223 / 50 : ℝ) - (223 / 50 : ℝ) - (287 / 100 : ℝ) * t)))) + (ind (1212451 / 731850 : ℝ) (123 / 50 : ℝ) t / (5 * t * (1 - t / (223 / 50 : ℝ))) * Real.log ((223 / 50 : ℝ) - 1 - t))) := by
  have hs : (tableParams ⟨(2 : Fin 9).val, by omega⟩).s = (12 / 5 : ℝ) := by simp [tableParams]; try norm_num
  have hsp : (tableParams ⟨(2 : Fin 9).val, by omega⟩).sp = (223 / 50 : ℝ) := by simp [tableParams]; try norm_num
  have hk1 : (tableParams ⟨(2 : Fin 9).val, by omega⟩).k1 = (357 / 100 : ℝ) := by simp [tableParams]; try norm_num
  have hk2 : (tableParams ⟨(2 : Fin 9).val, by omega⟩).k2 = (287 / 100 : ℝ) := by simp [tableParams]; try norm_num
  have hk3 : (tableParams ⟨(2 : Fin 9).val, by omega⟩).k3 = (12 / 5 : ℝ) := by simp [tableParams]; try norm_num
  have ha0 : alpha (tableParams ⟨(2 : Fin 9).val, by omega⟩) 0 = (157 / 100 : ℝ) := by simp [alpha, tableParams]; try norm_num
  have ha1 : alpha (tableParams ⟨(2 : Fin 9).val, by omega⟩) 1 = (123 / 50 : ℝ) := by simp [alpha, tableParams]; try norm_num
  have ha2 : alpha (tableParams ⟨(2 : Fin 9).val, by omega⟩) 2 = (961 / 600 : ℝ) := by simp [alpha, tableParams]; try norm_num
  have ha4 : alpha (tableParams ⟨(2 : Fin 9).val, by omega⟩) 4 = (961 / 600 : ℝ) := by simp [alpha, tableParams]; try norm_num
  have ha5 : alpha (tableParams ⟨(2 : Fin 9).val, by omega⟩) 5 = (19401 / 14350 : ℝ) := by simp [alpha, tableParams]; try norm_num
  have ha6 : alpha (tableParams ⟨(2 : Fin 9).val, by omega⟩) 6 = (96559 / 71400 : ℝ) := by simp [alpha, tableParams]; try norm_num
  have ha7 : alpha (tableParams ⟨(2 : Fin 9).val, by omega⟩) 7 = (1212451 / 731850 : ℝ) := by simp [alpha, tableParams]; try norm_num
  have ha8 : alpha (tableParams ⟨(2 : Fin 9).val, by omega⟩) 8 = (5437 / 4100 : ℝ) := by simp [alpha, tableParams]; try norm_num
  unfold tableKernel
  rw [dif_pos (by decide)]
  unfold Xi2
  dsimp only
  rw [ha0, ha1, ha2, ha4, ha5, ha6, ha7, ha8, hs, hsp, hk1, hk2, hk3]
  rw [(show (1024 : ℝ) / (((12 / 5 : ℝ) - 1) * ((223 / 50 : ℝ) - 1) * ((357 / 100 : ℝ) - 1) * ((287 / 100 : ℝ) - 1) * ((12 / 5 : ℝ) - 1)) = (12800000000 / 407396143 : ℝ) by norm_num),
      (show ((12 / 5 : ℝ) - 1) * ((223 / 50 : ℝ) - 1) * ((357 / 100 : ℝ) - 1) * ((287 / 100 : ℝ) - 1) * ((12 / 5 : ℝ) - 1) = (407396143 / 12500000 : ℝ) by norm_num),
      (show ((357 / 100 : ℝ) - 1) * ((287 / 100 : ℝ) - 1) = (48059 / 10000 : ℝ) by norm_num),
      (show (287 / 100 : ℝ) - 1 = (187 / 100 : ℝ) by norm_num),
      (show (357 / 100 : ℝ) - 1 = (257 / 100 : ℝ) by norm_num),
      (show (12 / 5 : ℝ) - 1 = (7 / 5 : ℝ) by norm_num),
      (show (223 / 50 : ℝ) - 1 = (173 / 50 : ℝ) by norm_num)]



theorem main_thm : (candidateMatrixQ 2 0 : ℝ) ≤ integralMatrix 2 0 := by
  have hcand : (candidateMatrixQ 2 0 : ℝ) = (1525199 / 10000000 : ℝ) := by simp [candidateMatrixQ]; try norm_num
  have hga : grid ⟨(0 : Fin 9).val, by omega⟩ = (1 : ℝ) := by simp [grid]; try norm_num
  have hgb : grid ⟨(0 : Fin 9).val + 1, by omega⟩ = (11 / 5 : ℝ) := by simp [grid]; try norm_num
  unfold integralMatrix
  rw [hcand, hga, hgb]
  have hint_eq : (∫ t in (1 : ℝ)..(11 / 5 : ℝ), tableKernel 2 t) =
      ∫ t in (1 : ℝ)..(11 / 5 : ℝ), ((((((((((sigma0 t / ((5 : ℝ) * t) * Real.log (12800000000 / 407396143 : ℝ)) + (ind (123 / 50 : ℝ) (3 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) ^ (5 : ℕ) / (407396143 / 12500000 : ℝ)))) + (ind (5437 / 4100 : ℝ) (157 / 100 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) / ((187 / 100 : ℝ) * ((257 / 100 : ℝ) - t))))) + (ind (961 / 600 : ℝ) (123 / 50 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) / ((7 / 5 : ℝ) * ((173 / 50 : ℝ) - t))))) + (ind (961 / 600 : ℝ) (123 / 50 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) / ((7 / 5 : ℝ) * ((173 / 50 : ℝ) - t))))) + (ind (157 / 100 : ℝ) (123 / 50 : ℝ) t / ((5 : ℝ) * t) * Real.log ((t + 1) ^ (2 : ℕ) / (48059 / 10000 : ℝ)))) + (ind (96559 / 71400 : ℝ) (961 / 600 : ℝ) t / (5 * t * (1 - t / (223 / 50 : ℝ))) * Real.log ((223 / 50 : ℝ) ^ (2 : ℕ) / (((357 / 100 : ℝ) * (223 / 50 : ℝ) - (223 / 50 : ℝ) - (357 / 100 : ℝ) * t) * ((12 / 5 : ℝ) * (223 / 50 : ℝ) - (223 / 50 : ℝ) - (12 / 5 : ℝ) * t))))) + (ind (961 / 600 : ℝ) (1212451 / 731850 : ℝ) t / (5 * t * (1 - t / (223 / 50 : ℝ))) * Real.log ((223 / 50 : ℝ) * ((223 / 50 : ℝ) - 1 - t) / ((357 / 100 : ℝ) * (223 / 50 : ℝ) - (223 / 50 : ℝ) - (357 / 100 : ℝ) * t)))) + (ind (19401 / 14350 : ℝ) (1212451 / 731850 : ℝ) t / (5 * t * (1 - t / (223 / 50 : ℝ))) * Real.log ((223 / 50 : ℝ) / ((287 / 100 : ℝ) * (223 / 50 : ℝ) - (223 / 50 : ℝ) - (287 / 100 : ℝ) * t)))) + (ind (1212451 / 731850 : ℝ) (123 / 50 : ℝ) t / (5 * t * (1 - t / (223 / 50 : ℝ))) * Real.log ((223 / 50 : ℝ) - 1 - t))) := by
    apply integral_congr; intro t _; exact hkern_eq t
  rw [hint_eq]
  exact le_trans (by norm_num) hsum_all_156.2

end
end W5Cert_R3_entry_2_0

theorem solution : (candidateMatrixQ 2 0 : ℝ) ≤ integralMatrix 2 0 :=
  W5Cert_R3_entry_2_0.main_thm
