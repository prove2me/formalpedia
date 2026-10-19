-- Prove2me | solution 1 for MarketInterference.FiniteSample.lemma_3
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-19T09:03:12.947732+00:00
-- url     : https://prove2.me/submissions/03238ee5-616f-40d1-ae7a-4274614d1da9

import Mathlib

set_option autoImplicit false

open MeasureTheory ProbabilityTheory NNReal Topology

noncomputable section

/-- Poisson weight. -/
def pw (l : ℝ) (n : ℕ) : ℝ := Real.exp (-l) * l ^ n / (Nat.factorial n : ℕ)

/-- shifted weight: `dpw l 0 = 0`, `dpw l (k+1) = pw l k`. -/
def dpw (l : ℝ) : ℕ → ℝ
  | 0 => 0
  | k + 1 => pw l k

/-- bound for `dpw`. -/
def dbd (L : ℝ) : ℕ → ℝ
  | 0 => 0
  | k + 1 => L ^ k / (Nat.factorial k : ℕ)

lemma pw_nonneg (l : ℝ) (hl : 0 ≤ l) (n : ℕ) : 0 ≤ pw l n := by
  unfold pw; positivity

lemma pw_le (l L : ℝ) (hl : 0 ≤ l) (hlL : l ≤ L) (n : ℕ) :
    pw l n ≤ L ^ n / (Nat.factorial n : ℕ) := by
  unfold pw
  have h1 : Real.exp (-l) ≤ 1 := by
    rw [Real.exp_le_one_iff]; linarith
  have h2 : l ^ n ≤ L ^ n := pow_le_pow_left₀ hl hlL n
  have h3 : (0 : ℝ) < (Nat.factorial n : ℕ) := by exact_mod_cast Nat.factorial_pos n
  rw [div_le_div_iff_of_pos_right h3]
  calc Real.exp (-l) * l ^ n ≤ 1 * l ^ n :=
        mul_le_mul_of_nonneg_right h1 (by positivity)
    _ ≤ L ^ n := by linarith

lemma dpw_le (l L : ℝ) (hl : 0 ≤ l) (hlL : l ≤ L) (n : ℕ) : dpw l n ≤ dbd L n := by
  cases n with
  | zero => simp [dpw, dbd]
  | succ k => exact pw_le l L hl hlL k

lemma dpw_nonneg (l : ℝ) (hl : 0 ≤ l) (n : ℕ) : 0 ≤ dpw l n := by
  cases n with
  | zero => simp [dpw]
  | succ k => exact pw_nonneg l hl k

lemma hasDerivAt_pw (l : ℝ) (n : ℕ) : HasDerivAt (fun l => pw l n) (dpw l n - pw l n) l := by
  cases n with
  | zero =>
    have h := (Real.hasDerivAt_exp (-l)).comp l (hasDerivAt_neg l)
    refine HasDerivAt.congr_deriv (f := fun l => pw l 0) (h.congr_of_eventuallyEq ?_) ?_
    · exact Filter.Eventually.of_forall fun y => by simp [pw]
    · simp [pw, dpw]
  | succ k =>
    have h1 := (Real.hasDerivAt_exp (-l)).comp l (hasDerivAt_neg l)
    have h2 := hasDerivAt_pow (k + 1) l
    have h3 := (h1.mul h2).div_const ((Nat.factorial (k + 1) : ℕ) : ℝ)
    refine HasDerivAt.congr_deriv (f := fun l => pw l (k + 1)) h3 ?_
    simp only [pw, dpw, Function.comp, Nat.add_sub_cancel]
    rw [Nat.factorial_succ]
    push_cast
    have : ((Nat.factorial k : ℕ) : ℝ) ≠ 0 := by positivity
    have : ((k : ℝ) + 1) ≠ 0 := by positivity
    field_simp
    ring

lemma summable_pow_two_mul (L : ℝ) (K : ℝ) :
    Summable (fun n : ℕ => K * ((2:ℝ) ^ n * (dbd L n + L ^ n / (Nat.factorial n : ℕ)))) := by
  refine Summable.mul_left K ?_
  have hs := Real.summable_pow_div_factorial (2 * L)
  refine (_root_.summable_nat_add_iff 1).mp ?_
  have h2 : Summable (fun n : ℕ => (2 * L) ^ (n + 1) / (Nat.factorial (n + 1) : ℕ)) :=
    (_root_.summable_nat_add_iff 1).mpr hs
  have := (hs.mul_left 2).add h2
  refine this.congr fun k => ?_
  simp only [dbd]
  rw [pow_succ, Nat.factorial_succ]
  push_cast
  have : ((Nat.factorial k : ℕ) : ℝ) ≠ 0 := by positivity
  have : ((k : ℝ) + 1) ≠ 0 := by positivity
  field_simp
  ring

lemma summable_pw_mul (h : ℕ → ℝ) (K : ℝ) (hK : 0 ≤ K) (hb : ∀ n, 0 ≤ h n ∧ h n ≤ K * 2 ^ n)
    (l : ℝ) (hl : 0 ≤ l) (L : ℝ) (hlL : l ≤ L) :
    Summable (fun n => pw l n * h n) := by
  have hs := (Real.summable_pow_div_factorial (2 * L)).mul_left K
  refine Summable.of_nonneg_of_le (fun n => mul_nonneg (pw_nonneg l hl n) (hb n).1) (fun n => ?_) hs
  calc pw l n * h n ≤ (L ^ n / (Nat.factorial n : ℕ)) * (K * 2 ^ n) :=
        mul_le_mul (pw_le l L hl hlL n) (hb n).2 (hb n).1
          (by have : (0:ℝ) ≤ L := hl.trans hlL; positivity)
    _ = K * ((2 * L) ^ n / (Nat.factorial n : ℕ)) := by
        rw [mul_pow]; ring

lemma tsum_deriv (h : ℕ → ℝ) (K : ℝ) (hK : 0 ≤ K) (hb : ∀ n, 0 ≤ h n ∧ h n ≤ K * 2 ^ n)
    (l : ℝ) (hl : 0 ≤ l) :
    ∑' n, (dpw l n - pw l n) * h n = ∑' n, pw l n * (h (n + 1) - h n) := by
  have hb' : ∀ n, 0 ≤ h (n + 1) ∧ h (n + 1) ≤ (2 * K) * 2 ^ n := fun n => by
    refine ⟨(hb (n + 1)).1, ?_⟩
    have := (hb (n + 1)).2
    calc h (n + 1) ≤ K * 2 ^ (n + 1) := this
      _ = (2 * K) * 2 ^ n := by ring
  have s1 : Summable (fun n => pw l n * h n) := summable_pw_mul h K hK hb l hl l le_rfl
  have s2 : Summable (fun n => pw l n * h (n + 1)) :=
    summable_pw_mul (fun n => h (n + 1)) (2 * K) (by positivity) hb' l hl l le_rfl
  have s3 : Summable (fun n => dpw l n * h n) := (_root_.summable_nat_add_iff 1).mp s2
  have e1 : ∑' n, dpw l n * h n = ∑' n, pw l n * h (n + 1) := by
    rw [Summable.tsum_eq_zero_add s3]
    simp [dpw]
  have e2 : ∀ n, (dpw l n - pw l n) * h n = dpw l n * h n - pw l n * h n := fun n => by ring
  have e3 : ∀ n, pw l n * (h (n + 1) - h n) = pw l n * h (n + 1) - pw l n * h n :=
    fun n => by ring
  simp only [e2, e3]
  rw [Summable.tsum_sub s3 s1, Summable.tsum_sub s2 s1, e1]

lemma main (h : ℕ → ℝ) (K : ℝ) (hK : 0 ≤ K) (hb : ∀ n, 0 ≤ h n ∧ h n ≤ K * 2 ^ n)
    (l₀ : ℝ) (hl₀ : 0 < l₀) :
    HasDerivAt (fun l : ℝ => ∑' n, pw l n * h n)
      (∑' n, pw l₀ n * (h (n + 1) - h n)) l₀ := by
  rw [← tsum_deriv h K hK hb l₀ hl₀.le]
  have := hasDerivAt_tsum_of_isPreconnected (g := fun n y => pw y n * h n)
    (g' := fun n y => (dpw y n - pw y n) * h n) (t := Set.Ioo 0 (2 * l₀))
    (u := fun n => K * (2 ^ n * (dbd (2 * l₀) n + (2 * l₀) ^ n / (Nat.factorial n : ℕ))))
    (y₀ := l₀) (y := l₀) (summable_pow_two_mul _ _) isOpen_Ioo isPreconnected_Ioo
    (fun n y _ => (hasDerivAt_pw y n).mul_const (h n)) ?_
    ⟨hl₀, by linarith⟩ (summable_pw_mul h K hK hb l₀ hl₀.le (2 * l₀) (by linarith)) ⟨hl₀, by linarith⟩
  · exact this
  · intro n y hy
    obtain ⟨hy0, hyL⟩ := hy
    have a1 := dpw_nonneg y hy0.le n
    have a2 := pw_nonneg y hy0.le n
    have b1 := dpw_le y (2 * l₀) hy0.le hyL.le n
    have b2 := pw_le y (2 * l₀) hy0.le hyL.le n
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hb n).1]
    have : |dpw y n - pw y n| ≤ dbd (2 * l₀) n + (2 * l₀) ^ n / (Nat.factorial n : ℕ) := by
      rw [abs_le]; constructor <;> linarith
    calc |dpw y n - pw y n| * h n
        ≤ (dbd (2 * l₀) n + (2 * l₀) ^ n / (Nat.factorial n : ℕ)) * (K * 2 ^ n) :=
          mul_le_mul this (hb n).2 (hb n).1 ((abs_nonneg _).trans this)
      _ = _ := by ring

theorem solution {m : ℕ} (x : Fin m → ℝ) (g : (Fin m → ℝ) → ℕ → ℝ) (M : ℝ)
    (hcont : ∀ d, Continuous fun y => g y d)
    (hg : ∀ y d, 0 ≤ g y d ∧ g y d ≤ M * ((d : ℝ) + ∑ k, |y k|))
    (l₀ : ℝ) (hl₀ : 0 < l₀) :
    HasDerivAt (fun l : ℝ => ∫ d, g x d ∂(poissonMeasure (Real.toNNReal l)))
      (∫ d, (g x (d + 1) - g x d) ∂(poissonMeasure (Real.toNNReal l₀))) l₀ := by
  set c : ℝ := ∑ k, |x k| with hc
  have hc0 : 0 ≤ c := Finset.sum_nonneg fun k _ => abs_nonneg _
  have hM : 0 ≤ M := by
    by_contra hneg
    push_neg at hneg
    have h1 := (hg x 1).2
    have h0 := (hg x 1).1
    have : M * (((1:ℕ) : ℝ) + c) < 0 := mul_neg_of_neg_of_pos hneg (by push_cast; linarith)
    linarith
  have hb : ∀ n, 0 ≤ g x n ∧ g x n ≤ (M * (c + 1)) * 2 ^ n := by
    intro n
    refine ⟨(hg x n).1, (hg x n).2.trans ?_⟩
    have h1 : (n : ℝ) ≤ 2 ^ n := by exact_mod_cast (Nat.lt_two_pow_self (n := n)).le
    have h2 : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
    have : (n : ℝ) + c ≤ (c + 1) * 2 ^ n := by nlinarith
    calc M * ((n : ℝ) + c) ≤ M * ((c + 1) * 2 ^ n) := mul_le_mul_of_nonneg_left this hM
      _ = _ := by ring
  have hmain := main (fun n => g x n) (M * (c + 1)) (by positivity) hb l₀ hl₀
  have e : ∀ l : ℝ, 0 < l → ∫ d, g x d ∂(poissonMeasure (Real.toNNReal l)) =
      ∑' n, pw l n * g x n := by
    intro l hl
    rw [integral_poissonMeasure]
    refine tsum_congr fun n => ?_
    simp [pw, Real.coe_toNNReal _ hl.le]
  have e' : ∫ d, (g x (d + 1) - g x d) ∂(poissonMeasure (Real.toNNReal l₀)) =
      ∑' n, pw l₀ n * (g x (n + 1) - g x n) := by
    rw [integral_poissonMeasure]
    refine tsum_congr fun n => ?_
    simp [pw, Real.coe_toNNReal _ hl₀.le]
  rw [e']
  refine hmain.congr_of_eventuallyEq ?_
  filter_upwards [Ioi_mem_nhds hl₀] with l hl using e l hl
