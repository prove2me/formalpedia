-- Prove2me | solution 1 for LinearChoresCLS.theorem_6_9
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-19T20:14:13.843861+00:00
-- url     : https://prove2.me/submissions/a5e833d2-0a5a-4cf1-8e54-72ffe4f3f6c5

import Mathlib
import Definitions.Def_LinearChoresCLS_Remainders
import Definitions.Def_LinearChoresCLS_RightDeriv

open Finset NetworkEquilibriumCLS.LinearNash LinearChoresCLS Filter Topology

namespace ChoresAux

/-- The chain quantities as functions of the two endpoint coordinates. -/
noncomputable def dS (t a b : ℝ) : ℕ → ℝ
  | 0 => Real.log ((1 + t * a) / (1 + t * b))
  | k + 1 => |dS t a b k| - 2 * Real.log (qPar t k)

/-- The chain remainder as a function of the two endpoint coordinates. -/
noncomputable def RF (w t : ℝ) (L : ℕ) (a b : ℝ) : ℝ :=
  (-(w / 2) * dS t a b L ^ 2 + w / 2 * ∑ k ∈ range L, (2 * Real.log (qPar t k)) ^ 2 +
    ∑ k ∈ range L, (w * t * (1 / 2 - 4 * t) ^ k / 2 - w * (2 * Real.log (qPar t k))) *
      |dS t a b k|) +
  w / 2 * (dS t a b 0 ^ 2 - t ^ 2 * (a - b) ^ 2)

lemma log_maxmin {u v q : ℝ} (hu : 0 < u) (hv : 0 < v) (hq : 0 < q) :
    Real.log ((max u v / q) / (q * min u v)) = |Real.log (u / v)| - 2 * Real.log q := by
  have hmn : 0 < min u v := lt_min hu hv
  have hmx : 0 < max u v := lt_max_of_lt_left hu
  rw [show (max u v / q) / (q * min u v) = (max u v / min u v) / q ^ 2 by
    field_simp]
  rw [Real.log_div (by positivity) (by positivity), Real.log_pow]
  push_cast
  rcases le_total v u with h | h
  · rw [max_eq_left h, min_eq_right h,
      abs_of_nonneg (Real.log_nonneg ((one_le_div hv).mpr h))]
  · rw [max_eq_right h, min_eq_left h,
      abs_of_nonpos (Real.log_nonpos (by positivity) ((div_le_one hv).mpr h))]
    rw [show v / u = (u / v)⁻¹ by field_simp, Real.log_inv]

lemma one_le_qPar {t : ℝ} (ht : 0 ≤ t) (ht8 : t ≤ 1 / 8) (k : ℕ) : 1 ≤ qPar t k := by
  unfold qPar
  have : 0 ≤ (1 / 2 - 4 * t) ^ k := pow_nonneg (by linarith) k
  nlinarith

lemma xExt_mem {n : ℕ} {x : Fin n → ℝ} (hx : InCube x) (i : Fin (n + 1)) :
    0 ≤ xExt x i ∧ xExt x i ≤ 1 := by
  refine Fin.cases ?_ (fun m => ?_) i
  · simp [xExt]
  · simpa [xExt] using hx m

lemma xbar_nonneg {n : ℕ} {x : Fin n → ℝ} (hx : InCube x) : 0 ≤ xbar x := by
  unfold xbar
  apply div_nonneg _ (by positivity)
  exact Finset.sum_nonneg (fun i _ => (xExt_mem hx i).1)

lemma chainDelta_eq {n : ℕ} {t : ℝ} (ht : 0 < t) (ht8 : t ≤ 1 / 8) (π : Pair n)
    {x : Fin n → ℝ} (hx : InCube x) (k : ℕ) :
    chainDelta t π x k = dS t (xExt x π.1.1) (xExt x π.1.2) k := by
  set a := xExt x π.1.1
  set b := xExt x π.1.2
  have hbar := xbar_nonneg hx
  have hp : ∀ i, 0 < basicPrice t x i := by
    intro i
    unfold basicPrice
    have := (xExt_mem hx i).1
    positivity
  have hratio : basicPrice t x π.1.1 / basicPrice t x π.1.2 = (1 + t * a) / (1 + t * b) := by
    unfold basicPrice
    have : (1 + t * xbar x) ≠ 0 := by positivity
    rw [div_div_div_cancel_right₀ this]
  have hq : ∀ k, 0 < qPar t k := fun k => lt_of_lt_of_le one_pos (one_le_qPar ht.le ht8 k)
  have main : ∀ k, 0 < (layerOut t (basicPrice t x π.1.1) (basicPrice t x π.1.2) k).1 ∧
      0 < (layerOut t (basicPrice t x π.1.1) (basicPrice t x π.1.2) k).2 ∧
      Real.log ((layerOut t (basicPrice t x π.1.1) (basicPrice t x π.1.2) k).1 /
        (layerOut t (basicPrice t x π.1.1) (basicPrice t x π.1.2) k).2) = dS t a b (k + 1) := by
    intro k
    induction k with
    | zero =>
      have h1 := hp π.1.1
      have h2 := hp π.1.2
      have hq0 := hq 0
      refine ⟨?_, ?_, ?_⟩
      · simp only [layerOut]; exact div_pos (lt_max_of_lt_left h1) hq0
      · simp only [layerOut]; exact mul_pos hq0 (lt_min h1 h2)
      · simp only [layerOut, dS]
        rw [log_maxmin h1 h2 hq0, hratio]
    | succ k ih =>
      obtain ⟨h1, h2, h3⟩ := ih
      have hqk := hq (k + 1)
      refine ⟨?_, ?_, ?_⟩
      · simp only [layerOut]; exact div_pos (lt_max_of_lt_left h1) hqk
      · simp only [layerOut]; exact mul_pos hqk (lt_min h1 h2)
      · simp only [layerOut]
        rw [log_maxmin h1 h2 hqk, h3]
        rfl
  cases k with
  | zero => simp only [chainDelta, dS]; rw [hratio]
  | succ k => simp only [chainDelta]; exact (main k).2.2

lemma chainRem_eq {n : ℕ} (P : Quadratic n) {t : ℝ} (ht : 0 < t) (ht8 : t ≤ 1 / 8) (L : ℕ)
    (π : Pair n) {x : Fin n → ℝ} (hx : InCube x) :
    chainRem P t L π x = RF (pairWeight P π) t L (xExt x π.1.1) (xExt x π.1.2) := by
  simp only [chainRem, RF, gadgetEarn, chainDelta_eq ht ht8 π hx]

lemma chainAbs_eq {n : ℕ} (P : Quadratic n) {t : ℝ} (ht : 0 < t) (ht8 : t ≤ 1 / 8) (L : ℕ)
    (π : Pair n) {x : Fin n → ℝ} (hx : InCube x) :
    chainAbs P t L π x = -(1 / 2) * ∑ k ∈ range L,
      pairWeight P π * t * (1 / 2 - 4 * t) ^ k * |dS t (xExt x π.1.1) (xExt x π.1.2) k| := by
  simp only [chainAbs, gadgetEarn, chainDelta_eq ht ht8 π hx]

/-- The telescoping identity behind (6.11). -/
lemma dS_tele (t a b : ℝ) (L : ℕ) :
    dS t a b L ^ 2 = dS t a b 0 ^ 2 + ∑ k ∈ range L, (2 * Real.log (qPar t k)) ^ 2 -
      2 * ∑ k ∈ range L, (2 * Real.log (qPar t k)) * |dS t a b k| := by
  induction L with
  | zero => simp
  | succ L ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    have : dS t a b (L + 1) = |dS t a b L| - 2 * Real.log (qPar t L) := rfl
    rw [this, sub_sq, sq_abs, ih]
    ring

lemma part1 (w t : ℝ) (L : ℕ) (a b : ℝ) :
    -(w / 2) * t ^ 2 * (a - b) ^ 2 =
      -(1 / 2) * ∑ k ∈ range L, w * t * (1 / 2 - 4 * t) ^ k * |dS t a b k| + RF w t L a b := by
  have tele := dS_tele t a b L
  have hS4 : ∑ k ∈ range L, (w * t * (1 / 2 - 4 * t) ^ k / 2 - w * (2 * Real.log (qPar t k))) *
      |dS t a b k| = (1 / 2) * ∑ k ∈ range L, w * t * (1 / 2 - 4 * t) ^ k * |dS t a b k| -
      w * ∑ k ∈ range L, (2 * Real.log (qPar t k)) * |dS t a b k| := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k _
    ring
  unfold RF
  rw [hS4]
  linear_combination (w / 2) * tele


/-! ## Stage B: bounds -/

lemma log_diff_le {t u v : ℝ} (ht : 0 ≤ t) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    Real.log (1 + t * u) - Real.log (1 + t * v) ≤ t * |u - v| := by
  have h1 : 0 < 1 + t * u := by positivity
  have h2 : 0 < 1 + t * v := by positivity
  rw [← Real.log_div h1.ne' h2.ne']
  have := Real.log_le_sub_one_of_pos (div_pos h1 h2)
  have h3 : (1 + t * u) / (1 + t * v) - 1 = t * (u - v) / (1 + t * v) := by
    field_simp; ring
  rw [h3] at this
  have h4 : t * (u - v) / (1 + t * v) ≤ t * |u - v| := by
    rw [div_le_iff₀ h2]
    have h5 : t * (u - v) ≤ t * |u - v| := mul_le_mul_of_nonneg_left (le_abs_self _) ht
    have h6 : 0 ≤ t * |u - v| * (t * v) := by positivity
    nlinarith
  linarith

lemma log_lip {t u v : ℝ} (ht : 0 ≤ t) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    |Real.log (1 + t * u) - Real.log (1 + t * v)| ≤ t * |u - v| := by
  rw [abs_le]
  constructor
  · have := log_diff_le ht hv hu
    rw [abs_sub_comm] at this
    linarith
  · exact log_diff_le ht hu hv

lemma dS_zero {t a b : ℝ} (ht : 0 ≤ t) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    dS t a b 0 = Real.log (1 + t * a) - Real.log (1 + t * b) := by
  simp only [dS]
  exact Real.log_div (by positivity) (by positivity)

lemma dS_lip {t a a' b : ℝ} (ht : 0 ≤ t) (ha : 0 ≤ a) (ha' : 0 ≤ a') (hb : 0 ≤ b) (k : ℕ) :
    |dS t a' b k - dS t a b k| ≤ t * |a' - a| := by
  induction k with
  | zero =>
    rw [dS_zero ht ha' hb, dS_zero ht ha hb]
    have := log_lip ht ha' ha
    rwa [show Real.log (1 + t * a') - Real.log (1 + t * b) -
      (Real.log (1 + t * a) - Real.log (1 + t * b)) =
      Real.log (1 + t * a') - Real.log (1 + t * a) by ring]
  | succ k ih =>
    simp only [dS]
    rw [show |dS t a' b k| - 2 * Real.log (qPar t k) - (|dS t a b k| - 2 * Real.log (qPar t k)) =
      |dS t a' b k| - |dS t a b k| by ring]
    exact (abs_abs_sub_abs_le_abs_sub _ _).trans ih

lemma dS0_bound {t a b : ℝ} (ht : 0 ≤ t) (ha : 0 ≤ a ∧ a ≤ 1) (hb : 0 ≤ b ∧ b ≤ 1) :
    |dS t a b 0| ≤ t := by
  rw [dS_zero ht ha.1 hb.1]
  refine (log_lip ht ha.1 hb.1).trans ?_
  have : |a - b| ≤ 1 := by rw [abs_le]; constructor <;> linarith
  nlinarith

/-- `g_k = (t/2) r^k - s_k`. -/
lemma g_bounds {t : ℝ} (ht : 0 ≤ t) (ht8 : t ≤ 1 / 8) (k : ℕ) :
    0 ≤ t / 2 * (1 / 2 - 4 * t) ^ k - 2 * Real.log (qPar t k) ∧
    t / 2 * (1 / 2 - 4 * t) ^ k - 2 * Real.log (qPar t k) ≤ t ^ 2 / 8 * (1 / 4) ^ k := by
  set r := 1 / 2 - 4 * t with hr
  have hr0 : 0 ≤ r := by rw [hr]; linarith
  have hr1 : r ≤ 1 / 2 := by rw [hr]; linarith
  set y := t / 4 * r ^ k with hy
  have hy0 : 0 ≤ y := by positivity
  have hq : qPar t k = 1 + y := by simp only [qPar, hy, hr]
  rw [hq]
  have hlog1 : Real.log (1 + y) ≤ y := by
    have := Real.log_le_sub_one_of_pos (show 0 < 1 + y by positivity); linarith
  have hlog2 : y / (1 + y) ≤ Real.log (1 + y) := by
    have := Real.one_sub_inv_le_log_of_pos (show 0 < 1 + y by positivity)
    have e : 1 - (1 + y)⁻¹ = y / (1 + y) := by field_simp; ring
    linarith
  have htr : t / 2 * r ^ k = 2 * y := by rw [hy]; ring
  rw [htr]
  have hyy : y - y / (1 + y) ≤ y ^ 2 := by
    rw [show y - y / (1 + y) = y ^ 2 / (1 + y) by field_simp; ring]
    exact div_le_self (by positivity) (by linarith)
  have hr2 : r ^ k * r ^ k ≤ (1 / 4) ^ k := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (by nlinarith) k
  have hy2 : 2 * y ^ 2 ≤ t ^ 2 / 8 * (1 / 4) ^ k := by
    rw [hy]
    have : 2 * (t / 4 * r ^ k) ^ 2 = t ^ 2 / 8 * (r ^ k * r ^ k) := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_left hr2 (by positivity)
  constructor <;> nlinarith

lemma s_le {t : ℝ} (ht : 0 ≤ t) (ht8 : t ≤ 1 / 8) (k : ℕ) :
    2 * Real.log (qPar t k) ≤ t * (1 / 2) ^ (k + 1) := by
  have h := (g_bounds ht ht8 k).1
  have hr : (1 / 2 - 4 * t) ^ k ≤ (1 / 2) ^ k :=
    pow_le_pow_left₀ (by linarith) (by linarith) k
  have : t / 2 * (1 / 2 - 4 * t) ^ k ≤ t * (1 / 2) ^ (k + 1) := by
    rw [pow_succ]; nlinarith
  linarith

lemma sum_g_le {t : ℝ} (ht : 0 ≤ t) (ht8 : t ≤ 1 / 8) (L : ℕ) :
    ∑ k ∈ range L, (t / 2 * (1 / 2 - 4 * t) ^ k - 2 * Real.log (qPar t k)) ≤ t ^ 2 / 6 := by
  have h1 : ∑ k ∈ range L, (t / 2 * (1 / 2 - 4 * t) ^ k - 2 * Real.log (qPar t k)) ≤
      ∑ k ∈ range L, t ^ 2 / 8 * (1 / 4 : ℝ) ^ k :=
    Finset.sum_le_sum (fun k _ => (g_bounds ht ht8 k).2)
  have h2 : ∑ k ∈ range L, (1 / 4 : ℝ) ^ k ≤ 4 / 3 := by
    rw [geom_sum_eq (by norm_num)]
    have : 0 ≤ (1 / 4 : ℝ) ^ L := by positivity
    rw [div_le_iff_of_neg (by norm_num)]
    linarith
  rw [← Finset.mul_sum] at h1
  nlinarith

lemma sum_half_sub_r {t : ℝ} (ht : 0 ≤ t) (ht8 : t ≤ 1 / 8) (L : ℕ) :
    ∑ k ∈ range L, ((1 / 2 : ℝ) ^ k - (1 / 2 - 4 * t) ^ k) ≤ 16 * t := by
  rw [Finset.sum_sub_distrib, geom_sum_eq (by norm_num)]
  set r := 1 / 2 - 4 * t with hr
  have hr0 : 0 ≤ r := by rw [hr]; linarith
  have hr1 : r ≤ 1 / 2 := by rw [hr]; linarith
  have hrL : r ^ L ≤ (1 / 2) ^ L := pow_le_pow_left₀ hr0 hr1 L
  have hrL0 : 0 ≤ r ^ L := pow_nonneg hr0 L
  have hhL : (1 / 2 : ℝ) ^ L ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  rw [geom_sum_eq (by linarith)]
  have hu : 0 < 1 - r := by linarith
  rw [show (r ^ L - 1) / (r - 1) = (1 - r ^ L) / (1 - r) by
    rw [← neg_sub, ← neg_sub 1 r, neg_div_neg_eq]]
  rw [show ((1 / 2 : ℝ) ^ L - 1) / (1 / 2 - 1) = 2 * (1 - (1 / 2) ^ L) by ring]
  -- (1 - r^L)/(1-r) ≥ (1 - h)/(1 - r)
  have h1 : (1 - (1 / 2 : ℝ) ^ L) / (1 - r) ≤ (1 - r ^ L) / (1 - r) :=
    div_le_div_of_nonneg_right (by linarith) hu.le
  have h2 : 2 * (1 - (1 / 2 : ℝ) ^ L) - (1 - (1 / 2) ^ L) / (1 - r) ≤ 16 * t := by
    have e : 1 - r = 1 / 2 + 4 * t := by rw [hr]; ring
    rw [e]
    have hpos : (0 : ℝ) < 1 / 2 + 4 * t := by linarith
    rw [sub_le_iff_le_add, ← sub_le_iff_le_add', le_div_iff₀ hpos]
    nlinarith
  linarith

/-- The comparison recurrence of the paper. -/
noncomputable def eS (t d0 : ℝ) : ℕ → ℝ
  | 0 => d0
  | k + 1 => |eS t d0 k| - t * (1 / 2) ^ (k + 1)

lemma eS_bound {t d0 : ℝ} (ht : 0 ≤ t) (hd : |d0| ≤ t) (k : ℕ) :
    |eS t d0 k| ≤ t * (1 / 2) ^ k := by
  induction k with
  | zero => simpa [eS] using hd
  | succ k ih =>
    simp only [eS]
    have h0 : 0 ≤ |eS t d0 k| := abs_nonneg _
    have e : t * (1 / 2 : ℝ) ^ k = 2 * (t * (1 / 2) ^ (k + 1)) := by rw [pow_succ]; ring
    rw [abs_le]
    constructor <;> nlinarith

lemma dS_eS {t a b : ℝ} (ht : 0 ≤ t) (ht8 : t ≤ 1 / 8) (k : ℕ) :
    |dS t a b k - eS t (dS t a b 0) k| ≤
      ∑ i ∈ range k, (t * (1 / 2) ^ (i + 1) - 2 * Real.log (qPar t i)) := by
  induction k with
  | zero => simp [eS]
  | succ k ih =>
    rw [Finset.sum_range_succ]
    rw [show dS t a b (k + 1) = |dS t a b k| - 2 * Real.log (qPar t k) from rfl,
      show eS t (dS t a b 0) (k + 1) = |eS t (dS t a b 0) k| - t * (1 / 2) ^ (k + 1) from rfl]
    have hs := s_le ht ht8 k
    have : |(|dS t a b k| - 2 * Real.log (qPar t k)) - (|eS t (dS t a b 0) k| - t * (1 / 2) ^ (k + 1))|
        ≤ |(|dS t a b k| - |eS t (dS t a b 0) k|)| + |t * (1 / 2) ^ (k + 1) - 2 * Real.log (qPar t k)| := by
      rw [show (|dS t a b k| - 2 * Real.log (qPar t k)) - (|eS t (dS t a b 0) k| - t * (1 / 2) ^ (k + 1)) =
        (|dS t a b k| - |eS t (dS t a b 0) k|) + (t * (1 / 2) ^ (k + 1) - 2 * Real.log (qPar t k)) by ring]
      exact abs_add_le _ _
    have h2 := abs_abs_sub_abs_le_abs_sub (dS t a b k) (eS t (dS t a b 0) k)
    rw [abs_of_nonneg (by linarith : 0 ≤ t * (1 / 2) ^ (k + 1) - 2 * Real.log (qPar t k))] at this
    linarith

lemma dS_L_bound {t a b : ℝ} {L : ℕ} (htL : t = (1 / 2) ^ L) (ht : 0 < t) (ht8 : t ≤ 1 / 8)
    (ha : 0 ≤ a ∧ a ≤ 1) (hb : 0 ≤ b ∧ b ≤ 1) : |dS t a b L| ≤ (9 + 1 / 6) * t ^ 2 := by
  have h1 := eS_bound ht.le (dS0_bound ht.le ha hb) L
  rw [← htL] at h1
  have h2 := dS_eS (a := a) (b := b) ht.le ht8 L
  have h3 : ∑ i ∈ range L, (t * (1 / 2) ^ (i + 1) - 2 * Real.log (qPar t i)) =
      t / 2 * ∑ i ∈ range L, ((1 / 2 : ℝ) ^ i - (1 / 2 - 4 * t) ^ i) +
      ∑ i ∈ range L, (t / 2 * (1 / 2 - 4 * t) ^ i - 2 * Real.log (qPar t i)) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [pow_succ]; ring
  have h4 := sum_half_sub_r ht.le ht8 L
  have h5 := sum_g_le ht.le ht8 L
  have h6 : |dS t a b L| ≤ |eS t (dS t a b 0) L| + |dS t a b L - eS t (dS t a b 0) L| := by
    have := abs_add_le (eS t (dS t a b 0) L) (dS t a b L - eS t (dS t a b 0) L)
    rwa [add_sub_cancel] at this
  have h7 : t / 2 * ∑ i ∈ range L, ((1 / 2 : ℝ) ^ i - (1 / 2 - 4 * t) ^ i) ≤ t / 2 * (16 * t) :=
    mul_le_mul_of_nonneg_left h4 (by positivity)
  nlinarith


/-! ## Stage C: the logarithmic remainder, Lipschitz bound, part 2 -/

lemma E_bound {t a b : ℝ} (ht : 0 < t) (ht8 : t ≤ 1 / 8) (ha : 0 ≤ a ∧ a ≤ 1)
    (hb : 0 ≤ b ∧ b ≤ 1) :
    |Real.log ((1 + t * a) / (1 + t * b)) / (1 + t * a) - t * (a - b)| ≤ 2 * t ^ 2 := by
  have hd : t * (a - b) = (1 + t * a) - (1 + t * b) := by ring
  rw [hd]
  generalize hu : 1 + t * a = u
  generalize hv : 1 + t * b = v
  have hu1 : 1 ≤ u := by rw [← hu]; nlinarith
  have hv1 : 1 ≤ v := by rw [← hv]; nlinarith
  have hut : u ≤ 1 + t := by rw [← hu]; nlinarith
  have hvt : v ≤ 1 + t := by rw [← hv]; nlinarith
  have hu0 : 0 < u := by linarith
  have hv0 : 0 < v := by linarith
  have hlo : (u - v) / u ≤ Real.log (u / v) := by
    have := Real.one_sub_inv_le_log_of_pos (div_pos hu0 hv0)
    rw [inv_div] at this
    have e : 1 - v / u = (u - v) / u := by field_simp
    linarith
  have hhi : Real.log (u / v) ≤ (u - v) / v := by
    have := Real.log_le_sub_one_of_pos (div_pos hu0 hv0)
    have e : u / v - 1 = (u - v) / v := by field_simp
    linarith
  have hduv : |u - v| ≤ t := by rw [abs_le]; constructor <;> linarith
  have hE1 : (u - v) / u / u - (u - v) ≤ Real.log (u / v) / u - (u - v) := by
    have := div_le_div_of_nonneg_right hlo hu0.le
    linarith
  have hE2 : Real.log (u / v) / u - (u - v) ≤ (u - v) / v / u - (u - v) := by
    have := div_le_div_of_nonneg_right hhi hu0.le
    linarith
  have hk1 : |(u - v) / u / u - (u - v)| ≤ 2 * t ^ 2 := by
    rw [show (u - v) / u / u - (u - v) = (u - v) * ((1 - u * u) / (u * u)) by
      field_simp]
    rw [abs_mul]
    have hX : |(1 - u * u) / (u * u)| ≤ 2 * t := by
      have huu : 0 < u * u := by positivity
      rw [abs_le]; constructor
      · rw [le_div_iff₀ huu]
        have h1 : u * u ≤ (1 + t) * (1 + t) := by nlinarith
        have h2 : u * u * (1 - 2 * t) ≤ (1 + t) * (1 + t) * (1 - 2 * t) :=
          mul_le_mul_of_nonneg_right h1 (by linarith)
        have h3 : (1 + t) * (1 + t) * (1 - 2 * t) ≤ 1 := by nlinarith [sq_nonneg t]
        nlinarith
      · rw [div_le_iff₀ huu]; nlinarith
    calc |u - v| * |(1 - u * u) / (u * u)| ≤ t * (2 * t) :=
          mul_le_mul hduv hX (abs_nonneg _) ht.le
      _ = 2 * t ^ 2 := by ring
  have hk2 : |(u - v) / v / u - (u - v)| ≤ 2 * t ^ 2 := by
    rw [show (u - v) / v / u - (u - v) = (u - v) * ((1 - v * u) / (v * u)) by
      field_simp]
    rw [abs_mul]
    have hX : |(1 - v * u) / (v * u)| ≤ 2 * t := by
      have hvu : 0 < v * u := by positivity
      rw [abs_le]; constructor
      · rw [le_div_iff₀ hvu]
        have h1 : v * u ≤ (1 + t) * (1 + t) := by nlinarith
        have h2 : v * u * (1 - 2 * t) ≤ (1 + t) * (1 + t) * (1 - 2 * t) :=
          mul_le_mul_of_nonneg_right h1 (by linarith)
        have h3 : (1 + t) * (1 + t) * (1 - 2 * t) ≤ 1 := by nlinarith [sq_nonneg t]
        nlinarith
      · rw [div_le_iff₀ hvu]; nlinarith
    calc |u - v| * |(1 - v * u) / (v * u)| ≤ t * (2 * t) :=
          mul_le_mul hduv hX (abs_nonneg _) ht.le
      _ = 2 * t ^ 2 := by ring
  rw [abs_le]
  constructor
  · have := (abs_le.mp hk1).1; linarith
  · have := (abs_le.mp hk2).2; linarith

lemma phi_lip {t a a' b : ℝ} (ht : 0 < t) (ht8 : t ≤ 1 / 8) (ha : 0 ≤ a ∧ a ≤ 1)
    (ha' : 0 ≤ a' ∧ a' ≤ 1) (hb : 0 ≤ b ∧ b ≤ 1) :
    |(dS t a' b 0 ^ 2 - t ^ 2 * (a' - b) ^ 2) - (dS t a b 0 ^ 2 - t ^ 2 * (a - b) ^ 2)| ≤
      4 * t ^ 3 * |a' - a| := by
  let φ : ℝ → ℝ := fun z => Real.log ((1 + t * z) / (1 + t * b)) ^ 2 - t ^ 2 * (z - b) ^ 2
  let φ' : ℝ → ℝ := fun z =>
    2 * t * (Real.log ((1 + t * z) / (1 + t * b)) / (1 + t * z) - t * (z - b))
  have hd : ∀ z ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt φ (φ' z) (Set.Icc 0 1) z := by
    intro z hz
    have hu : 0 < 1 + t * z := by have := hz.1; positivity
    have hv : 0 < 1 + t * b := by have := hb.1; positivity
    have h1 : HasDerivAt (fun z => (1 + t * z) / (1 + t * b)) (t / (1 + t * b)) z := by
      have := (((hasDerivAt_id z).const_mul t).const_add 1).div_const (1 + t * b)
      simpa using this
    have h2 := (h1.log (div_pos hu hv).ne').pow 2
    have h4 : HasDerivAt (fun z => t ^ 2 * (z - b) ^ 2) (t ^ 2 * (2 * (z - b))) z := by
      have := (((hasDerivAt_id z).sub_const b).pow 2).const_mul (t ^ 2)
      simpa using this
    have h5 := h2.sub h4
    apply HasDerivAt.hasDerivWithinAt
    have hfun : φ = ((fun y => Real.log ((1 + t * y) / (1 + t * b))) ^ 2 -
        fun z => t ^ 2 * (z - b) ^ 2) := by
      funext y
      simp [φ]
    rw [hfun]
    convert h5 using 1
    simp only [φ']
    norm_num
    field_simp
  have hbound : ∀ z ∈ Set.Icc (0 : ℝ) 1, ‖φ' z‖ ≤ 4 * t ^ 3 := by
    intro z hz
    rw [Real.norm_eq_abs]
    simp only [φ']
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * t)]
    have := E_bound ht ht8 ⟨hz.1, hz.2⟩ hb
    calc 2 * t * |Real.log ((1 + t * z) / (1 + t * b)) / (1 + t * z) - t * (z - b)|
        ≤ 2 * t * (2 * t ^ 2) := by gcongr
      _ = 4 * t ^ 3 := by ring
  have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hd hbound (convex_Icc 0 1)
    ⟨ha.1, ha.2⟩ ⟨ha'.1, ha'.2⟩
  simpa [φ, dS, Real.norm_eq_abs] using this

lemma RF_lip {w t : ℝ} {L : ℕ} (hw : 0 ≤ w) (htL : t = (1 / 2) ^ L) (ht : 0 < t)
    (ht8 : t ≤ 1 / 8) {a a' b : ℝ} (ha : 0 ≤ a ∧ a ≤ 1) (ha' : 0 ≤ a' ∧ a' ≤ 1)
    (hb : 0 ≤ b ∧ b ≤ 1) :
    |RF w t L a' b - RF w t L a b| ≤ 12 * w * t ^ 3 * |a' - a| := by
  set δ := |a' - a| with hδdef
  have hδ : 0 ≤ δ := abs_nonneg _
  set c : ℕ → ℝ := fun k => w * t * (1 / 2 - 4 * t) ^ k / 2 - w * (2 * Real.log (qPar t k))
    with hcdef
  have hc : ∀ k, c k = w * (t / 2 * (1 / 2 - 4 * t) ^ k - 2 * Real.log (qPar t k)) :=
    fun k => by simp only [hcdef]; ring
  have hc0 : ∀ k, 0 ≤ c k := fun k => by rw [hc]; exact mul_nonneg hw (g_bounds ht.le ht8 k).1
  have hcsum : ∑ k ∈ range L, c k ≤ w * (t ^ 2 / 6) := by
    simp_rw [hc]
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (sum_g_le ht.le ht8 L) hw
  have hsplit : RF w t L a' b - RF w t L a b =
      -(w / 2) * ((dS t a' b L - dS t a b L) * (dS t a' b L + dS t a b L)) +
      ∑ k ∈ range L, c k * (|dS t a' b k| - |dS t a b k|) +
      w / 2 * ((dS t a' b 0 ^ 2 - t ^ 2 * (a' - b) ^ 2) -
        (dS t a b 0 ^ 2 - t ^ 2 * (a - b) ^ 2)) := by
    have : ∑ k ∈ range L, c k * (|dS t a' b k| - |dS t a b k|) =
        ∑ k ∈ range L, c k * |dS t a' b k| - ∑ k ∈ range L, c k * |dS t a b k| := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro k _
      ring
    rw [this]
    simp only [RF, hcdef]
    ring
  rw [hsplit]
  have hL' := dS_L_bound htL ht ht8 ha' hb
  have hL := dS_L_bound htL ht ht8 ha hb
  have hlipL := dS_lip ht.le ha.1 ha'.1 hb.1 L
  have hT1 : |-(w / 2) * ((dS t a' b L - dS t a b L) * (dS t a' b L + dS t a b L))| ≤
      w * ((9 + 1 / 6) * t ^ 2) * (t * δ) := by
    rw [abs_mul, abs_mul, abs_neg, abs_of_nonneg (by positivity : 0 ≤ w / 2)]
    have hsum : |dS t a' b L + dS t a b L| ≤ 2 * ((9 + 1 / 6) * t ^ 2) :=
      (abs_add_le _ _).trans (by linarith)
    calc w / 2 * (|dS t a' b L - dS t a b L| * |dS t a' b L + dS t a b L|)
        ≤ w / 2 * ((t * δ) * (2 * ((9 + 1 / 6) * t ^ 2))) := by gcongr
      _ = w * ((9 + 1 / 6) * t ^ 2) * (t * δ) := by ring
  have hT2 : |∑ k ∈ range L, c k * (|dS t a' b k| - |dS t a b k|)| ≤
      w * (t ^ 2 / 6) * (t * δ) := by
    calc |∑ k ∈ range L, c k * (|dS t a' b k| - |dS t a b k|)|
        ≤ ∑ k ∈ range L, |c k * (|dS t a' b k| - |dS t a b k|)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ range L, c k * (t * δ) := by
        apply Finset.sum_le_sum
        intro k _
        rw [abs_mul, abs_of_nonneg (hc0 k)]
        exact mul_le_mul_of_nonneg_left
          ((abs_abs_sub_abs_le_abs_sub _ _).trans (dS_lip ht.le ha.1 ha'.1 hb.1 k)) (hc0 k)
      _ = (∑ k ∈ range L, c k) * (t * δ) := by rw [Finset.sum_mul]
      _ ≤ w * (t ^ 2 / 6) * (t * δ) := by
        apply mul_le_mul_of_nonneg_right hcsum
        positivity
  have hT3 : |w / 2 * ((dS t a' b 0 ^ 2 - t ^ 2 * (a' - b) ^ 2) -
        (dS t a b 0 ^ 2 - t ^ 2 * (a - b) ^ 2))| ≤ w / 2 * (4 * t ^ 3 * δ) := by
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ w / 2)]
    gcongr
    exact phi_lip ht ht8 ha ha' hb
  have hsum3 := abs_add_three
    (-(w / 2) * ((dS t a' b L - dS t a b L) * (dS t a' b L + dS t a b L)))
    (∑ k ∈ range L, c k * (|dS t a' b k| - |dS t a b k|))
    (w / 2 * ((dS t a' b 0 ^ 2 - t ^ 2 * (a' - b) ^ 2) - (dS t a b 0 ^ 2 - t ^ 2 * (a - b) ^ 2)))
  have hpos : 0 ≤ w * t ^ 3 * δ := by positivity
  nlinarith

lemma dS_swap {t a b : ℝ} (ht : 0 ≤ t) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ∀ k, |dS t b a k| = |dS t a b k| ∧ dS t b a k ^ 2 = dS t a b k ^ 2 := by
  have h0 : dS t b a 0 = -dS t a b 0 := by
    rw [dS_zero ht hb ha, dS_zero ht ha hb]; ring
  have hsucc : ∀ k, dS t b a (k + 1) = dS t a b (k + 1) := by
    intro k
    induction k with
    | zero =>
      show |dS t b a 0| - 2 * Real.log (qPar t 0) = |dS t a b 0| - 2 * Real.log (qPar t 0)
      rw [h0, abs_neg]
    | succ k ih =>
      show |dS t b a (k + 1)| - 2 * Real.log (qPar t (k + 1)) =
        |dS t a b (k + 1)| - 2 * Real.log (qPar t (k + 1))
      rw [ih]
  intro k
  cases k with
  | zero => rw [h0, abs_neg, neg_sq]; exact ⟨rfl, rfl⟩
  | succ k => rw [hsucc k]; exact ⟨rfl, rfl⟩

lemma RF_symm {w t : ℝ} {L : ℕ} (ht : 0 ≤ t) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    RF w t L a b = RF w t L b a := by
  have hsw := dS_swap ht ha hb
  simp only [RF]
  rw [(hsw L).2, (hsw 0).2]
  have : ∑ k ∈ range L, (w * t * (1 / 2 - 4 * t) ^ k / 2 - w * (2 * Real.log (qPar t k))) *
      |dS t b a k| = ∑ k ∈ range L, (w * t * (1 / 2 - 4 * t) ^ k / 2 -
        w * (2 * Real.log (qPar t k))) * |dS t a b k| :=
    Finset.sum_congr rfl (fun k _ => by rw [(hsw k).1])
  rw [this]
  ring

lemma pairWeight_nonneg {n : ℕ} (P : Quadratic n) (π : Pair n) : 0 ≤ pairWeight P π := by
  set S := ∑ i, ∑ j, |(P.Q i j : ℝ)| + ∑ i, |(P.c i : ℝ)| with hS
  have hA0 : 0 ≤ ∑ i, ∑ j, |(P.Q i j : ℝ)| := by positivity
  have hC0 : 0 ≤ ∑ i, |(P.c i : ℝ)| := by positivity
  have hS0 : 0 ≤ S := by positivity
  have hlam : lam P = 1 / (2 * ((n : ℝ) + 1) * (1 + S)) := by
    simp only [lam, hS]; ring_nf
  have hlam0 : 0 ≤ lam P := by rw [hlam]; positivity
  have key : ∀ z : ℝ, |z| ≤ S →
      0 ≤ 1 / ((n : ℝ) + 1) - lam P * z ∧ 0 ≤ 1 / ((n : ℝ) + 1) + lam P * z := by
    intro z hz
    have h1 : lam P * |z| ≤ lam P * S := mul_le_mul_of_nonneg_left hz hlam0
    have h2 : lam P * S ≤ 1 / ((n : ℝ) + 1) := by
      rw [hlam, div_mul_eq_mul_div, one_mul, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    have h3 : |lam P * z| ≤ lam P * S := by rw [abs_mul, abs_of_nonneg hlam0]; exact h1
    have h4 := abs_le.mp h3
    constructor <;> linarith [h4.1, h4.2]
  have hj' : π.1.2 ≠ 0 := by
    intro h
    have := π.2
    rw [h] at this
    exact absurd this (Fin.not_lt_zero _)
  have hrow : ∀ i : Fin n, ∑ k, |(P.Q i k : ℝ)| ≤ S := by
    intro i
    have := Finset.single_le_sum (f := fun i => ∑ k, |(P.Q i k : ℝ)|)
      (fun i _ => by positivity) (Finset.mem_univ i)
    linarith
  unfold pairWeight wgt
  split_ifs with h1
  · apply (key _ _).1
    exact (Finset.abs_sum_le_sum_abs _ _).trans (hrow _)
  · apply (key _ _).2
    refine le_trans ?_ (hrow (π.1.1.pred h1))
    exact Finset.single_le_sum (f := fun k => |(P.Q (π.1.1.pred h1) k : ℝ)|)
      (fun _ _ => abs_nonneg _) (Finset.mem_univ _)

lemma tParam_facts {n : ℕ} (P : Quadratic n) (ε : ℚ) :
    tParam P ε = (1 / 2) ^ chainLength P ε ∧ 0 < tParam P ε ∧ tParam P ε ≤ 1 / 8 := by
  have hL : 8 ≤ chainLength P ε := by
    unfold chainLength
    split_ifs with h
    · exact (Nat.find_spec h).1
    · exact le_refl _
  refine ⟨rfl, by unfold tParam; positivity, ?_⟩
  unfold tParam
  calc ((1 : ℝ) / 2) ^ chainLength P ε ≤ (1 / 2) ^ 8 :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) hL
    _ ≤ 1 / 8 := by norm_num

lemma xExt_add_single {n : ℕ} (x : Fin n → ℝ) (ℓ : Fin n) (h : ℝ) (i : Fin (n + 1)) :
    xExt (x + h • Pi.single ℓ (1 : ℝ)) i = xExt x i + if i = ℓ.succ then h else 0 := by
  refine Fin.cases ?_ (fun m => ?_) i
  · simp [xExt, (Fin.succ_ne_zero ℓ).symm]
  · simp only [xExt, Fin.cons_succ, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Fin.succ_inj]
    by_cases hm : m = ℓ
    · subst hm; simp
    · simp [hm, Pi.single_apply]

theorem part2 {n : ℕ} (P : Quadratic n) (ε : ℚ) (π : Pair n) (x : Fin n → ℝ) (ℓ : Fin n)
    (h : ℝ) (hx : InCube x) (hy : InCube (x + h • Pi.single ℓ (1 : ℝ))) :
    |chainRem P (tParam P ε) (chainLength P ε) π (x + h • Pi.single ℓ (1 : ℝ)) -
      chainRem P (tParam P ε) (chainLength P ε) π x| ≤
      12 * pairWeight P π * tParam P ε ^ 3 * |h| := by
  obtain ⟨htL, ht, ht8⟩ := tParam_facts P ε
  have hw := pairWeight_nonneg P π
  rw [chainRem_eq P ht ht8 _ π hy, chainRem_eq P ht ht8 _ π hx]
  have hjj : π.1.1 ≠ π.1.2 := ne_of_lt π.2
  have ea := xExt_add_single x ℓ h π.1.1
  have eb := xExt_add_single x ℓ h π.1.2
  have ha := xExt_mem hx π.1.1
  have hb := xExt_mem hx π.1.2
  have ha' := xExt_mem hy π.1.1
  have hb' := xExt_mem hy π.1.2
  rw [ea] at ha' ⊢
  rw [eb] at hb' ⊢
  by_cases h1 : π.1.1 = ℓ.succ
  · have h2 : π.1.2 ≠ ℓ.succ := fun h2 => hjj (h1.trans h2.symm)
    rw [if_pos h1] at ha' ⊢
    rw [if_neg h2, add_zero] at hb' ⊢
    have := RF_lip hw htL ht ht8 ha ha' hb
    rwa [add_sub_cancel_left] at this
  · rw [if_neg h1, add_zero] at ha' ⊢
    by_cases h2 : π.1.2 = ℓ.succ
    · rw [if_pos h2] at hb' ⊢
      rw [RF_symm ht.le ha.1 hb'.1, RF_symm ht.le ha.1 hb.1]
      have := RF_lip (L := chainLength P ε) (w := pairWeight P π) hw htL ht ht8 hb hb' ha
      rwa [add_sub_cancel_left] at this
    · rw [if_neg h2, add_zero, sub_self, abs_zero]
      positivity


/-! ## Stage D: right derivatives, part 3 -/

/-- Existence of a finite right derivative at `0`. -/
def RD (f : ℝ → ℝ) : Prop := ∃ D, HasDerivWithinAt f D (Set.Ioi 0) 0

lemma RD_of_diff {f : ℝ → ℝ} (hf : DifferentiableAt ℝ f 0) : RD f :=
  ⟨_, hf.hasDerivAt.hasDerivWithinAt⟩

lemma RD_const (c : ℝ) : RD (fun _ => c) := ⟨0, hasDerivWithinAt_const _ _ _⟩

lemma RD_add {f g : ℝ → ℝ} (hf : RD f) (hg : RD g) : RD (fun h => f h + g h) := by
  obtain ⟨D, hD⟩ := hf; obtain ⟨E, hE⟩ := hg; exact ⟨_, hD.add hE⟩

lemma RD_sub {f g : ℝ → ℝ} (hf : RD f) (hg : RD g) : RD (fun h => f h - g h) := by
  obtain ⟨D, hD⟩ := hf; obtain ⟨E, hE⟩ := hg; exact ⟨_, hD.sub hE⟩

lemma RD_mul {f g : ℝ → ℝ} (hf : RD f) (hg : RD g) : RD (fun h => f h * g h) := by
  obtain ⟨D, hD⟩ := hf; obtain ⟨E, hE⟩ := hg; exact ⟨_, hD.mul hE⟩

lemma RD_sq {f : ℝ → ℝ} (hf : RD f) : RD (fun h => f h ^ 2) := by
  have := RD_mul hf hf
  simpa [sq] using this

lemma RD_abs {f : ℝ → ℝ} (hf : RD f) : RD (fun h => |f h|) := by
  obtain ⟨D, hD⟩ := hf
  by_cases h0 : f 0 = 0
  · refine ⟨|D|, ?_⟩
    have hs : (0 : ℝ) ∉ Set.Ioi 0 := by simp
    rw [hasDerivWithinAt_iff_tendsto_slope' hs] at hD ⊢
    have := hD.abs
    apply this.congr'
    filter_upwards [self_mem_nhdsWithin] with h hh
    have hh' : 0 < h := hh
    simp only [slope_def_field, h0, abs_zero, sub_zero]
    rw [abs_div, abs_of_pos hh']
  · exact ⟨_, (hasDerivAt_abs h0).comp_hasDerivWithinAt 0 hD⟩

lemma RD_sum (F : ℕ → ℝ → ℝ) (hF : ∀ k, RD (F k)) (L : ℕ) :
    RD (fun h => ∑ k ∈ range L, F k h) := by
  induction L with
  | zero => simpa using RD_const 0
  | succ L ih =>
    simp only [Finset.sum_range_succ]
    exact RD_add ih (hF L)

lemma RD_dS (t a b α β : ℝ) (ht : 0 ≤ t) (ha : 0 ≤ a) (hb : 0 ≤ b) (k : ℕ) :
    RD (fun h => dS t (a + α * h) (b + β * h) k) := by
  induction k with
  | zero =>
    apply RD_of_diff
    show DifferentiableAt ℝ (fun h => Real.log ((1 + t * (a + α * h)) / (1 + t * (b + β * h)))) 0
    have h1 : DifferentiableAt ℝ (fun h : ℝ => 1 + t * (a + α * h)) 0 := by fun_prop
    have h2 : DifferentiableAt ℝ (fun h : ℝ => 1 + t * (b + β * h)) 0 := by fun_prop
    have hb0 : (1 + t * (b + β * 0)) ≠ 0 := by
      have : 0 < 1 + t * b := by positivity
      simpa using this.ne'
    have ha0 : (1 + t * (a + α * 0)) / (1 + t * (b + β * 0)) ≠ 0 := by
      have h3 : 0 < 1 + t * a := by positivity
      have h4 : 0 < 1 + t * b := by positivity
      simpa using (div_pos h3 h4).ne'
    exact (h1.div h2 hb0).log ha0
  | succ k ih =>
    show RD (fun h => |dS t (a + α * h) (b + β * h) k| - 2 * Real.log (qPar t k))
    exact RD_sub (RD_abs ih) (RD_const _)

lemma RD_RF (w t : ℝ) (L : ℕ) (a b α β : ℝ) (ht : 0 ≤ t) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    RD (fun h => RF w t L (a + α * h) (b + β * h)) := by
  have hD := RD_dS t a b α β ht ha hb
  show RD (fun h =>
    (-(w / 2) * dS t (a + α * h) (b + β * h) L ^ 2 +
      w / 2 * ∑ k ∈ range L, (2 * Real.log (qPar t k)) ^ 2 +
      ∑ k ∈ range L, (w * t * (1 / 2 - 4 * t) ^ k / 2 - w * (2 * Real.log (qPar t k))) *
        |dS t (a + α * h) (b + β * h) k|) +
    w / 2 * (dS t (a + α * h) (b + β * h) 0 ^ 2 - t ^ 2 * ((a + α * h) - (b + β * h)) ^ 2))
  refine RD_add (RD_add (RD_add (RD_mul (RD_const _) (RD_sq (hD L))) (RD_const _)) ?_) ?_
  · exact RD_sum (fun k h => (w * t * (1 / 2 - 4 * t) ^ k / 2 - w * (2 * Real.log (qPar t k))) *
      |dS t (a + α * h) (b + β * h) k|) (fun k => RD_mul (RD_const _) (RD_abs (hD k))) L
  · refine RD_mul (RD_const _) (RD_sub (RD_sq (hD 0)) ?_)
    apply RD_of_diff
    fun_prop

theorem part3 {n : ℕ} (P : Quadratic n) (ε : ℚ) (π : Pair n) (x : Fin n → ℝ) (ℓ : Fin n)
    (s : Bool) (hx : InCube x) (hfeas : FeasibleCoordDir x ℓ s) :
    ∃ D : ℝ, HasRightDerivAt0
        (fun h => chainRem P (tParam P ε) (chainLength P ε) π (x + h • coordDir ℓ s)) D ∧
      |D| ≤ 12 * pairWeight P π * tParam P ε ^ 3 := by
  obtain ⟨htL, ht, ht8⟩ := tParam_facts P ε
  have hw := pairWeight_nonneg P π
  set σ : ℝ := if s then 1 else -1 with hσ
  have hσ1 : |σ| = 1 := by rw [hσ]; split_ifs <;> simp
  have hcd : ∀ h : ℝ, x + h • coordDir ℓ s = x + (h * σ) • Pi.single ℓ (1 : ℝ) := by
    intro h
    funext i
    simp only [coordDir, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply, hσ]
    split_ifs <;> ring
  set α : ℝ := if π.1.1 = ℓ.succ then σ else 0 with hα
  set β : ℝ := if π.1.2 = ℓ.succ then σ else 0 with hβ
  have ha := xExt_mem hx π.1.1
  have hb := xExt_mem hx π.1.2
  have hxe : ∀ (h : ℝ) i, xExt (x + h • coordDir ℓ s) i =
      xExt x i + if i = ℓ.succ then h * σ else 0 := by
    intro h i; rw [hcd]; exact xExt_add_single x ℓ (h * σ) i
  have hAeq : ∀ h : ℝ, xExt (x + h • coordDir ℓ s) π.1.1 = xExt x π.1.1 + α * h := by
    intro h; rw [hxe, hα]; split_ifs <;> ring
  have hBeq : ∀ h : ℝ, xExt (x + h • coordDir ℓ s) π.1.2 = xExt x π.1.2 + β * h := by
    intro h; rw [hxe, hβ]; split_ifs <;> ring
  set γ : ℝ → ℝ := fun h => chainRem P (tParam P ε) (chainLength P ε) π (x + h • coordDir ℓ s)
    with hγdef
  set M : ℝ → ℝ := fun h => RF (pairWeight P π) (tParam P ε) (chainLength P ε)
    (xExt x π.1.1 + α * h) (xExt x π.1.2 + β * h) with hMdef
  have hEq : ∀ h, InCube (x + h • coordDir ℓ s) → γ h = M h := by
    intro h hc
    simp only [hγdef, hMdef]
    rw [chainRem_eq P ht ht8 _ π hc, hAeq, hBeq]
  have hx0 : x + (0 : ℝ) • coordDir ℓ s = x := by simp
  have h0 : γ 0 = M 0 := hEq 0 (by rw [hx0]; exact hx)
  obtain ⟨D, hD⟩ := RD_RF (pairWeight P π) (tParam P ε) (chainLength P ε)
    (xExt x π.1.1) (xExt x π.1.2) α β ht.le ha.1 hb.1
  have hγ : HasDerivWithinAt γ D (Set.Ioi 0) 0 := by
    apply hD.congr_of_eventuallyEq _ h0
    filter_upwards [hfeas] with h hc using hEq h hc
  have hs : (0 : ℝ) ∉ Set.Ioi 0 := by simp
  have hT := (hasDerivWithinAt_iff_tendsto_slope' hs).mp hγ
  refine ⟨D, ?_, ?_⟩
  · unfold HasRightDerivAt0
    refine hT.congr (fun h => ?_)
    simp only [slope_def_module, sub_zero]
  · have hTa := (continuous_abs.tendsto D).comp hT
    apply le_of_tendsto hTa
    filter_upwards [hfeas, self_mem_nhdsWithin] with h hc hpos
    have hpos' : 0 < h := hpos
    simp only [Function.comp, slope_def_field, sub_zero]
    have key := part2 P ε π x ℓ (h * σ) hx (by rw [← hcd]; exact hc)
    rw [← hcd, abs_mul, hσ1, mul_one, abs_of_pos hpos'] at key
    have hγ0 : γ 0 = chainRem P (tParam P ε) (chainLength P ε) π x := by
      simp only [hγdef, hx0]
    rw [hγ0, abs_div, abs_of_pos hpos', div_le_iff₀ hpos']
    exact key

end ChoresAux

open ChoresAux in
theorem solution {n : ℕ} (hn : 0 < n) (P : Quadratic n) (ε : ℚ) (hε : 0 < ε) (π : Pair n) :
    (∀ x : Fin n → ℝ, InCube x →
      -(pairWeight P π / 2) * tParam P ε ^ 2 * (xExt x π.1.1 - xExt x π.1.2) ^ 2 =
        chainAbs P (tParam P ε) (chainLength P ε) π x +
          chainRem P (tParam P ε) (chainLength P ε) π x) ∧
    (∀ (x : Fin n → ℝ) (ℓ : Fin n) (h : ℝ), InCube x → InCube (x + h • Pi.single ℓ (1 : ℝ)) →
      |chainRem P (tParam P ε) (chainLength P ε) π (x + h • Pi.single ℓ (1 : ℝ)) -
          chainRem P (tParam P ε) (chainLength P ε) π x| ≤
        12 * pairWeight P π * tParam P ε ^ 3 * |h|) ∧
    (∀ (x : Fin n → ℝ) (ℓ : Fin n) (s : Bool), InCube x → FeasibleCoordDir x ℓ s →
      ∃ D : ℝ, HasRightDerivAt0
          (fun h => chainRem P (tParam P ε) (chainLength P ε) π (x + h • coordDir ℓ s)) D ∧
        |D| ≤ 12 * pairWeight P π * tParam P ε ^ 3) := by
  obtain ⟨htL, ht, ht8⟩ := tParam_facts P ε
  refine ⟨fun x hx => ?_, fun x ℓ h hx hy => part2 P ε π x ℓ h hx hy,
    fun x ℓ s hx hf => part3 P ε π x ℓ s hx hf⟩
  rw [chainAbs_eq P ht ht8 _ π hx, chainRem_eq P ht ht8 _ π hx]
  exact part1 _ _ _ _ _
