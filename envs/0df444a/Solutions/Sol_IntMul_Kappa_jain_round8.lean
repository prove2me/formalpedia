-- Prove2me | solution 1 for IntMul.Kappa.jain_round8
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-11T19:59:36.871714+00:00
-- url     : https://prove2.me/submissions/77380b78-ea32-4bc7-8a6b-674ab06fd398
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_IntMul_MultitapeModel
import Definitions.Def_IntMul_KappaFramework
import Definitions.Def_IntMul_KappaJainData
import Theorems.Thm_IntMul_Kappa_jain_round8_framework

/-!
Rational certificates for Jain's round eight, made sound over ℝ.

`lnUp` is a rigorous upper bound for `log` (from `Real.abs_log_sub_add_sum_range_le`),
`expUp` for `exp` on `[0, 1]` (`Real.exp_bound'`), and `momentOK` certifies the real moment
inequality `∑ n_w (w/m)^(1-a) < W` (`histMoment_lt`).
-/

namespace IntMul.KappaCert

open IntMul.Kappa

/-- Round a rational up to the grid `2^-128`. -/
def rup (q : ℚ) : ℚ := (Int.ceil (q * 2 ^ 128 : ℚ) : ℚ) / 2 ^ 128

theorem le_rup (q : ℚ) : q ≤ rup q := by
  unfold rup
  rw [le_div_iff₀ (by positivity)]
  exact Int.le_ceil _

/-- `∑_{i<n} x^(i+1)/(i+1)`, the partial sum of `-log(1-x)`. -/
def lsum (x : ℚ) : ℕ → ℚ
  | 0 => 0
  | i + 1 => lsum x i + x ^ (i + 1) / (i + 1)

theorem lsum_eq (x : ℚ) (n : ℕ) :
    ((lsum x n : ℚ) : ℝ) = ∑ i ∈ Finset.range n, (x : ℝ) ^ (i + 1) / (i + 1) := by
  induction n with
  | zero => simp [lsum]
  | succ n ih => rw [lsum, Finset.sum_range_succ, ← ih]; push_cast; ring

/-- Upper bound for `-log(1-x)` for `0 ≤ x < 1`. -/
def nlogUp (x : ℚ) (n : ℕ) : ℚ := lsum x n + x ^ (n + 1) / (1 - x)

theorem neg_log_le_nlogUp (x : ℚ) (n : ℕ) (h0 : 0 ≤ x) (h1 : x < 1) :
    -Real.log (1 - (x : ℝ)) ≤ (nlogUp x n : ℝ) := by
  have hx0 : (0 : ℝ) ≤ x := by exact_mod_cast h0
  have hx1 : (x : ℝ) < 1 := by exact_mod_cast h1
  have habs : |(x : ℝ)| < 1 := by rw [abs_of_nonneg hx0]; exact hx1
  have key := Real.abs_log_sub_add_sum_range_le habs n
  rw [abs_of_nonneg hx0] at key
  have := (abs_le.mp key).1
  unfold nlogUp
  push_cast
  rw [lsum_eq]
  linarith

/-- Halve `x` while it exceeds `2`, counting the halvings. -/
def halve (x : ℚ) (k : ℕ) : ℕ → ℚ × ℕ
  | 0 => (x, k)
  | f + 1 => if 2 < x then halve (x / 2) (k + 1) f else (x, k)

theorem halve_spec (x : ℚ) (k f : ℕ) (hx : 1 ≤ x) :
    1 ≤ (halve x k f).1 ∧ x * 2 ^ k = (halve x k f).1 * 2 ^ (halve x k f).2 := by
  induction f generalizing x k with
  | zero => simp [halve, hx]
  | succ f ih =>
    unfold halve
    split_ifs with h
    · obtain ⟨h1, h2⟩ := ih (x / 2) (k + 1) (by linarith)
      refine ⟨h1, ?_⟩
      rw [← h2]; ring
    · simp [hx]

/-- Upper bound for `log 2`. -/
def log2Up : ℚ := rup (nlogUp (1 / 2) 100)

theorem log_two_le : Real.log 2 ≤ (log2Up : ℝ) := by
  have h := neg_log_le_nlogUp (1 / 2) 100 (by norm_num) (by norm_num)
  have e : -Real.log (1 - ((1 / 2 : ℚ) : ℝ)) = Real.log 2 := by
    rw [← Real.log_inv]; norm_num
  rw [e] at h
  unfold log2Up
  exact h.trans (by exact_mod_cast le_rup _)

/-- Upper bound for `log x` when `1 ≤ x`. -/
def lnUp (x : ℚ) : ℚ :=
  let p := halve x 0 64
  rup (p.2 * log2Up + nlogUp (1 - 1 / p.1) 100)

theorem log_le_lnUp (x : ℚ) (hx : 1 ≤ x) : Real.log x ≤ (lnUp x : ℝ) := by
  obtain ⟨h1, h2⟩ := halve_spec x 0 64 hx
  set y := (halve x 0 64).1 with hy
  set k := (halve x 0 64).2 with hk
  simp only [pow_zero, mul_one] at h2
  have hy0 : (0 : ℝ) < y := by exact_mod_cast (show (0 : ℚ) < y by linarith)
  have hy1 : (1 : ℝ) ≤ y := by exact_mod_cast h1
  have hxr : (x : ℝ) = y * 2 ^ k := by exact_mod_cast h2
  have hlogx : Real.log x = Real.log y + k * Real.log 2 := by
    rw [hxr, Real.log_mul hy0.ne' (by positivity), Real.log_pow]
  have hz0 : (0 : ℚ) ≤ 1 - 1 / y := by
    rw [sub_nonneg, div_le_one (by linarith)]; exact h1
  have hz1 : 1 - 1 / y < 1 := by
    have : (0 : ℚ) < 1 / y := by apply div_pos one_pos; linarith
    linarith
  have hser := neg_log_le_nlogUp (1 - 1 / y) 100 hz0 hz1
  have e : -Real.log (1 - (((1 - 1 / y : ℚ)) : ℝ)) = Real.log y := by
    push_cast
    rw [show (1 : ℝ) - (1 - 1 / (y : ℝ)) = (y : ℝ)⁻¹ by ring, Real.log_inv, neg_neg]
  rw [e] at hser
  have hl2 := log_two_le
  have hkr : (0 : ℝ) ≤ k := by positivity
  unfold lnUp
  simp only
  rw [← hy, ← hk]
  refine le_trans ?_ (show (((k : ℚ) * log2Up + nlogUp (1 - 1 / y) 100 : ℚ) : ℝ) ≤ _ by
    exact_mod_cast le_rup _)
  push_cast
  rw [hlogx]
  nlinarith

/-- Partial exponential series `∑_{m<n} u^m/m!`. -/
def esum (u : ℚ) : ℕ → ℚ
  | 0 => 0
  | m + 1 => esum u m + u ^ m / (m.factorial : ℚ)

theorem esum_eq (u : ℚ) (n : ℕ) :
    ((esum u n : ℚ) : ℝ) = ∑ m ∈ Finset.range n, (u : ℝ) ^ m / (m.factorial : ℝ) := by
  induction n with
  | zero => simp [esum]
  | succ n ih => rw [esum, Finset.sum_range_succ, ← ih]; push_cast; ring

/-- Upper bound for `exp u` when `0 ≤ u ≤ 1` (Mathlib's `Real.exp_bound'`). -/
def expUp (u : ℚ) (n : ℕ) : ℚ := esum u n + u ^ n * (n + 1) / ((n.factorial : ℚ) * n)

theorem exp_le_expUp (u : ℚ) (n : ℕ) (hn : 0 < n) (h0 : 0 ≤ u) (h1 : u ≤ 1) :
    Real.exp u ≤ (expUp u n : ℝ) := by
  have h := Real.exp_bound' (x := (u : ℝ)) (by exact_mod_cast h0) (by exact_mod_cast h1) hn
  unfold expUp
  push_cast
  rw [esum_eq]
  exact h

/-- the exponent `a log(m/w)`, rounded up -/
def expo (a : ℚ) (m w : ℕ) : ℚ := rup (a * lnUp ((m : ℚ) / w))

def termOK (a : ℚ) (m : ℕ) (p : ℕ × ℕ) : Bool :=
  decide (0 < p.1) && decide (p.1 ≤ m) && decide (0 ≤ expo a m p.1) && decide (expo a m p.1 ≤ 1)

def termUp (a : ℚ) (m n : ℕ) (p : ℕ × ℕ) : ℚ :=
  rup ((p.2 : ℚ) * ((p.1 : ℚ) / m) * expUp (expo a m p.1) n)

/-- Rational moment certificate: every child width lies in `(0, m]`, and the rounded-up
exponential majorant of the moment is below `W`. -/
def momentOK (h : List (ℕ × ℕ)) (a : ℚ) (m W n : ℕ) : Bool :=
  h.all (termOK a m) && decide ((h.map (termUp a m n)).sum < W)

theorem term_le (a : ℚ) (m n : ℕ) (p : ℕ × ℕ) (ha : 0 ≤ a) (hn : 0 < n)
    (hp : termOK a m p = true) :
    (p.2 : ℝ) * ((p.1 : ℝ) / m) ^ (1 - (a : ℝ)) ≤ (termUp a m n p : ℝ) := by
  simp only [termOK, Bool.and_eq_true, decide_eq_true_eq] at hp
  obtain ⟨⟨⟨hw0, hwm⟩, hu0⟩, hu1⟩ := hp
  have hwR : (0 : ℝ) < p.1 := by exact_mod_cast hw0
  have hmR : (0 : ℝ) < m := by exact_mod_cast (lt_of_lt_of_le hw0 hwm)
  have hwmR : (p.1 : ℝ) ≤ m := by exact_mod_cast hwm
  have hq1 : (1 : ℚ) ≤ (m : ℚ) / p.1 := by
    rw [le_div_iff₀ (by exact_mod_cast hw0)]; simpa using (show ((p.1 : ℚ)) ≤ m by exact_mod_cast hwm)
  have hlog := log_le_lnUp _ hq1
  have hrp : ((p.1 : ℝ) / m) ^ (1 - (a : ℝ)) = ((p.1 : ℝ) / m) * Real.exp (a * Real.log ((m : ℝ) / p.1)) := by
    rw [Real.rpow_def_of_pos (div_pos hwR hmR), mul_sub, mul_one, Real.exp_sub, Real.exp_log (div_pos hwR hmR)]
    rw [div_eq_mul_inv _ (Real.exp _), ← Real.exp_neg]
    congr 2
    rw [Real.log_div hmR.ne' hwR.ne', Real.log_div hwR.ne' hmR.ne']; ring
  have haR : (0 : ℝ) ≤ a := by exact_mod_cast ha
  have hexpo : (a : ℝ) * Real.log ((m : ℝ) / p.1) ≤ (expo a m p.1 : ℝ) := by
    unfold expo
    have : (((m : ℚ) / p.1 : ℚ) : ℝ) = (m : ℝ) / p.1 := by push_cast; rfl
    rw [this] at hlog
    calc (a : ℝ) * Real.log ((m : ℝ) / p.1) ≤ a * (lnUp ((m : ℚ) / p.1) : ℝ) :=
          mul_le_mul_of_nonneg_left hlog haR
      _ = ((a * lnUp ((m : ℚ) / p.1) : ℚ) : ℝ) := by push_cast; rfl
      _ ≤ _ := by exact_mod_cast le_rup _
  have hexp : Real.exp (a * Real.log ((m : ℝ) / p.1)) ≤ (expUp (expo a m p.1) n : ℝ) :=
    (Real.exp_le_exp.mpr hexpo).trans (exp_le_expUp _ n hn hu0 hu1)
  rw [hrp]
  unfold termUp
  refine le_trans ?_ (show (((p.2 : ℚ) * ((p.1 : ℚ) / m) * expUp (expo a m p.1) n : ℚ) : ℝ) ≤ _ by
    exact_mod_cast le_rup _)
  push_cast
  rw [← mul_assoc]
  apply mul_le_mul_of_nonneg_left hexp
  positivity

theorem histMoment_lt (h : List (ℕ × ℕ)) (a : ℚ) (m W n : ℕ) (ha : 0 ≤ a) (hn : 0 < n)
    (hc : momentOK h a m W n = true) : histMoment h m (1 - (a : ℝ)) < W := by
  simp only [momentOK, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hc
  obtain ⟨hall, hsum⟩ := hc
  have hle : histMoment h m (1 - (a : ℝ)) ≤ (((h.map (termUp a m n)).sum : ℚ) : ℝ) := by
    unfold histMoment
    clear hsum
    induction h with
    | nil => simp
    | cons p t ih =>
      simp only [List.map_cons, List.sum_cons]
      push_cast
      have h1 := term_le a m n p ha hn (hall p (by simp))
      have h2 := ih (fun q hq => hall q (by simp [hq]))
      push_cast at h2
      linarith
  have : (((h.map (termUp a m n)).sum : ℚ) : ℝ) < W := by exact_mod_cast hsum
  linarith

end IntMul.KappaCert

open IntMul.KappaCert IntMul.Kappa

set_option maxRecDepth 100000 in
theorem r8_bitOld_ok : momentOK Jain.bitR7plain (12899 / 200000000) 529 104719230 6 = true := by
  decide +kernel
set_option maxRecDepth 100000 in
theorem r8_bit_ok : momentOK Jain.bitR8 (25367 / 200000000) 529 104719230 6 = true := by
  decide +kernel
set_option maxRecDepth 100000 in
theorem r8_cx_ok : momentOK Jain.cxR8 (3945999 / 31250000000) 576 12869228 6 = true := by
  decide +kernel
theorem r8_rank : histRankSum Jain.cxR8 = 7410813248 := by decide +kernel
theorem r8_log : lnUp 7410813248 < 227264 / 10000 := by decide +kernel

theorem solution : IntMul.KappaBound (0.00012612978530233 : ℝ) := by
  have h1 := histMoment_lt _ _ _ _ _ (by norm_num) (by norm_num) r8_bitOld_ok
  have h2 := histMoment_lt _ _ _ _ _ (by norm_num) (by norm_num) r8_bit_ok
  have h3 := histMoment_lt _ _ _ _ _ (by norm_num) (by norm_num) r8_cx_ok
  have hl : Real.log (7410813248 : ℕ) < 227264 / 10000 := by
    have := log_le_lnUp 7410813248 (by norm_num)
    have h' : ((lnUp 7410813248 : ℚ) : ℝ) < ((227264 / 10000 : ℚ) : ℝ) := by exact_mod_cast r8_log
    push_cast at this h' ⊢
    linarith
  push_cast at h1 h2 h3
  refine jain_round8_framework (12899 / 200000000) (25367 / 200000000) (6338633 / 50000000000)
    (3945999 / 31250000000) (399949548085879 / 400000000000000) 13093 13093 _
    (by norm_num) (by norm_num) (by norm_num) h1 h2 (by norm_num) (by norm_num) h3 ?_
  rw [r8_rank]
  unfold CrudeAssembly
  norm_num
  push_cast at hl
  linarith
