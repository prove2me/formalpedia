-- Prove2me | solution 1 for JuschenkoMonod.tendsto_F
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-29T20:55:06.816631+00:00
-- url     : https://prove2.me/submissions/c021c330-e4cb-4026-ab07-646ef3f580d1

import Mathlib
import Definitions.Def_IntervalExchange
import Definitions.Def_JuschenkoMonod
import Theorems.Thm_JuschenkoMonod_abs_B_le_four_mul_wobblingNorm_sq
import Theorems.Thm_JuschenkoMonod_tsum_a_mul_exp_le_three_and_tsum_a_sq_mul_exp_le_inv

namespace JuschenkoMonod

open Finset Real

/-- Abel summation bound. -/
lemma tF_abel_identity (ψ b : ℕ → ℝ) (N : ℕ) :
    ∑ k ∈ range (N + 1), ψ k * b k =
      ψ N * ∑ k ∈ range (N + 1), b k -
        ∑ k ∈ range N, (ψ (k + 1) - ψ k) * ∑ i ∈ range (k + 1), b i := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_range_succ (fun k => ψ k * b k), ih, sum_range_succ (fun k => (ψ (k + 1) - ψ k) * _),
      sum_range_succ b (N + 1)]
    ring

lemma tF_abel_bound (ψ b : ℕ → ℝ) (M : ℝ) (hB : ∀ N, |∑ k ∈ range (N + 1), b k| ≤ M) (N : ℕ) :
    |∑ k ∈ range (N + 1), ψ k * b k| ≤
      M * (|ψ N| + ∑ k ∈ range N, |ψ (k + 1) - ψ k|) := by
  rw [tF_abel_identity]
  have hM : 0 ≤ M := le_trans (abs_nonneg _) (hB 0)
  calc _ ≤ |ψ N * ∑ k ∈ range (N + 1), b k| +
        |∑ k ∈ range N, (ψ (k + 1) - ψ k) * ∑ i ∈ range (k + 1), b i| := abs_sub _ _
    _ ≤ |ψ N| * M + ∑ k ∈ range N, |ψ (k + 1) - ψ k| * M := by
      gcongr
      · rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hB N) (abs_nonneg _)
      · refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun k _ => ?_)
        rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hB k) (abs_nonneg _)
    _ = _ := by rw [← sum_mul]; ring

/-- The one-step estimate for `ψ(s) = s u/(1+u)`, `u = exp(-N s)^2`. -/
lemma tF_step (N t s : ℝ) (hN : 1 ≤ N) (ht : N * t = 1) (hs : 0 < s) :
    |exp (-N * (s * exp (-t))) ^ 2 / (1 + exp (-N * (s * exp (-t))) ^ 2) * (s * exp (-t)) -
        exp (-N * s) ^ 2 / (1 + exp (-N * s) ^ 2) * s| ≤
      t * (exp (-N * s) * s) + 6 * (exp (-N * (s * exp (-t))) ^ 2 * (s * exp (-t)) ^ 2) := by
  have ht0 : 0 < t := by
    by_contra h; have h := not_lt.mp h; nlinarith
  have ht1 : t ≤ 1 := by nlinarith
  set s' := s * exp (-t) with hs'def
  set u := exp (-N * s) ^ 2 with hu
  set u' := exp (-N * s') ^ 2 with hu'
  set α := exp (-N * s) with hα
  have hα0 : 0 < α := exp_pos _
  have hα1 : α ≤ 1 := by rw [hα]; apply Real.exp_le_one_iff.mpr; nlinarith
  have hs'0 : 0 < s' := mul_pos hs (exp_pos _)
  have het : exp (-t) * exp t = 1 := by rw [← Real.exp_add]; simp
  have he3 : exp t ≤ 3 := by
    have := Real.exp_one_lt_d9
    have : exp t ≤ exp 1 := Real.exp_le_exp.mpr ht1
    linarith
  have hst : s = s' * exp t := by rw [hs'def, mul_assoc, het, mul_one]
  have h1 : 0 ≤ s - s' := by
    rw [hs'def]
    have : exp (-t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    nlinarith
  have h2 : s - s' ≤ t * s := by
    rw [hs'def]
    have := Real.add_one_le_exp (-t)
    nlinarith
  -- u = u' * exp(-2N(s - s'))
  have huu : u = u' * exp (-(2 * N * (s - s'))) := by
    rw [hu, hu', ← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add]
    congr 1; push_cast; ring
  have hu'0 : 0 ≤ u' := by positivity
  have hu0 : 0 ≤ u := by positivity
  have h3 : 0 ≤ u' - u := by
    rw [huu]
    have : exp (-(2 * N * (s - s'))) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    nlinarith
  have h4 : u' - u ≤ u' * (2 * N * (s - s')) := by
    rw [huu]
    have := Real.add_one_le_exp (-(2 * N * (s - s')))
    nlinarith
  have h5 : u' - u ≤ 6 * u' * s' := by
    have : 2 * N * (s - s') ≤ 6 * s' := by
      have : N * (s - s') ≤ s := by nlinarith
      rw [hst] at this ⊢
      nlinarith
    nlinarith
  have hw : u' / (1 + u') - u / (1 + u) = (u' - u) / ((1 + u') * (1 + u)) := by
    field_simp; ring
  have hw1 : 0 ≤ u' / (1 + u') - u / (1 + u) := by rw [hw]; positivity
  have hw2 : u' / (1 + u') - u / (1 + u) ≤ u' - u := by
    rw [hw]; apply div_le_self h3; nlinarith
  have hw3 : u / (1 + u) ≤ u := div_le_self hu0 (by linarith)
  have hw4 : 0 ≤ u / (1 + u) := by positivity
  have huα : u ≤ α := by rw [hu]; nlinarith
  have key : u' / (1 + u') * s' - u / (1 + u) * s =
      s' * (u' / (1 + u') - u / (1 + u)) - (s - s') * (u / (1 + u)) := by ring
  rw [key]
  refine (abs_sub _ _).trans ?_
  rw [abs_of_nonneg (mul_nonneg hs'0.le hw1), abs_of_nonneg (mul_nonneg h1 hw4)]
  have e1 : s' * (u' / (1 + u') - u / (1 + u)) ≤ 6 * (u' * s' ^ 2) := by
    calc _ ≤ s' * (6 * u' * s') := by
          apply mul_le_mul_of_nonneg_left (hw2.trans h5) hs'0.le
      _ = _ := by ring
  have e2 : (s - s') * (u / (1 + u)) ≤ t * (α * s) := by
    calc _ ≤ (t * s) * α := mul_le_mul h2 (hw3.trans huα) hw4 (by positivity)
      _ = _ := by ring
  linarith

noncomputable def tF_phi1 (n : ℕ) (j : ℤ) : ℝ := a n j * Real.exp (-(|j| : ℝ) / n)
noncomputable def tF_phi2 (n : ℕ) (j : ℤ) : ℝ := a n j ^ 2 * Real.exp (-2 * (|j| : ℝ) / n)
noncomputable def tF_f (n : ℕ) (g : Equiv.Perm ℤ) (j : ℤ) : ℝ :=
  a n j ^ 2 / (1 + a n j ^ 2) * Real.exp (-(|j| : ℝ) / n) * ((|g j| : ℝ) - |j|)
noncomputable def tF_psi (n : ℕ) (k : ℕ) : ℝ :=
  a n k ^ 2 / (1 + a n k ^ 2) * Real.exp (-(|(k : ℤ)| : ℝ) / n)

lemma tF_abs_nat (k : ℕ) : (|((k : ℤ) : ℝ)|) = (k : ℝ) := by
  rw [Int.cast_natCast, Nat.abs_cast]

lemma tF_a_nonneg (n : ℕ) (j : ℤ) : 0 ≤ a n j := (Real.exp_pos _).le

lemma tF_a_le_one (n : ℕ) (j : ℤ) : a n j ≤ 1 := by
  unfold a; apply Real.exp_le_one_iff.mpr
  have := Real.exp_pos (-(|j| : ℝ) / n)
  have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  nlinarith

lemma tF_psi_step (n k : ℕ) (hn : 0 < n) :
    |tF_psi n (k + 1) - tF_psi n k| ≤ 1 / n * tF_phi1 n k + 6 * tF_phi2 n ((k + 1 : ℕ) : ℤ) := by
  have hN : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have ht : (n : ℝ) * (1 / n) = 1 := by field_simp
  have hs : 0 < exp (-(k : ℝ) / n) := exp_pos _
  have h := tF_step n (1 / n) (exp (-(k : ℝ) / n)) hN ht hs
  have hs' : exp (-(k : ℝ) / n) * exp (-(1 / (n : ℝ))) = exp (-((k + 1 : ℕ) : ℝ) / n) := by
    rw [← exp_add]; congr 1; push_cast; ring
  have hsq : exp (-((k + 1 : ℕ) : ℝ) / n) ^ 2 = exp (-2 * ((k + 1 : ℕ) : ℝ) / n) := by
    rw [← exp_nat_mul]; congr 1; push_cast; ring
  rw [hs', hsq] at h
  simp only [tF_psi, tF_phi1, tF_phi2, a, tF_abs_nat]
  convert h using 2

lemma tF_psi_le (n k : ℕ) (hn : 0 < n) : |tF_psi n k| ≤ 1 / n := by
  have hN : (0 : ℝ) < n := by exact_mod_cast hn
  have ha0 := tF_a_nonneg n k
  have ha1 := tF_a_le_one n k
  have hs : 0 < exp (-(k : ℝ) / n) := exp_pos _
  unfold tF_psi
  rw [tF_abs_nat, abs_of_nonneg (by positivity)]
  have h1 : a n k ^ 2 / (1 + a n k ^ 2) ≤ a n k := by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  have h2 : a n k * exp (-(k : ℝ) / n) ≤ 1 / n := by
    unfold a
    rw [Int.cast_natCast, Nat.abs_cast]
    set s := exp (-(k : ℝ) / n)
    have he := Real.add_one_le_exp ((n : ℝ) * s)
    have hm : exp (-(n : ℝ) * s) * exp ((n : ℝ) * s) = 1 := by rw [← exp_add]; simp
    have hp := exp_pos (-(n : ℝ) * s)
    rw [le_div_iff₀ hN]
    nlinarith
  calc _ ≤ a n k * exp (-(k : ℝ) / n) := mul_le_mul_of_nonneg_right h1 hs.le
    _ ≤ _ := h2

lemma tF_sum_le_tsum (f : ℤ → ℝ) (hf0 : ∀ j, 0 ≤ f j) (hf : Summable f) (e : ℕ ↪ ℤ) (m : ℕ) :
    ∑ k ∈ range m, f (e k) ≤ ∑' j, f j := by
  rw [← Finset.sum_map (range m) e f]
  exact hf.sum_le_tsum _ (fun j _ => hf0 j)

lemma tF_var_le (n m : ℕ) (hn : 0 < n) :
    |tF_psi n m| + ∑ k ∈ range m, |tF_psi n (k + 1) - tF_psi n k| ≤ 10 / n := by
  have hN : (0 : ℝ) < n := by exact_mod_cast hn
  obtain ⟨hs1, h1, hs2, h2⟩ := tsum_a_mul_exp_le_three_and_tsum_a_sq_mul_exp_le_inv n hn
  have hp1 : ∀ j, 0 ≤ tF_phi1 n j := fun j => mul_nonneg (tF_a_nonneg n j) (exp_pos _).le
  have hp2 : ∀ j, 0 ≤ tF_phi2 n j := fun j => mul_nonneg (pow_nonneg (tF_a_nonneg n j) 2) (exp_pos _).le
  have e1 : ∑ k ∈ range m, tF_phi1 n k ≤ 3 :=
    (tF_sum_le_tsum (tF_phi1 n) hp1 hs1 Nat.castEmbedding m).trans h1
  let e : ℕ ↪ ℤ := ⟨fun k => ((k + 1 : ℕ) : ℤ), fun x y hxy => by simpa using hxy⟩
  have e2 : ∑ k ∈ range m, tF_phi2 n ((k + 1 : ℕ) : ℤ) ≤ 1 / n :=
    (tF_sum_le_tsum (tF_phi2 n) hp2 hs2 e m).trans h2
  have hstep : ∑ k ∈ range m, |tF_psi n (k + 1) - tF_psi n k| ≤
      ∑ k ∈ range m, (1 / n * tF_phi1 n k + 6 * tF_phi2 n ((k + 1 : ℕ) : ℤ)) :=
    sum_le_sum fun k _ => tF_psi_step n k hn
  rw [sum_add_distrib, ← mul_sum, ← mul_sum] at hstep
  have hpsi := tF_psi_le n m hn
  have : 1 / (n : ℝ) * ∑ k ∈ range m, tF_phi1 n k ≤ 1 / n * 3 :=
    mul_le_mul_of_nonneg_left e1 (by positivity)
  have h10 : (10 : ℝ) / n = 1 / n + 1 / n * 3 + 6 * (1 / n) := by ring
  rw [h10]
  linarith

theorem tendsto_F_aux (g : Equiv.Perm ℤ) (hg : g ∈ IntervalExchange.wobbling ℤ) :
    Filter.Tendsto (fun n => F n g) Filter.atTop (nhds 0) := by
  obtain ⟨C, hC⟩ := hg
  have hbdd : BddAbove (Set.range fun j : ℤ => |((g j : ℤ) : ℝ) - j|) := by
    refine ⟨C, ?_⟩
    rintro _ ⟨j, rfl⟩
    have := hC j
    rwa [Int.dist_eq] at this
  have hc : ∀ j : ℤ, |((g j : ℤ) : ℝ) - j| ≤ wobblingNorm g := fun j => le_ciSup hbdd j
  set c := wobblingNorm g with hcdef
  have hB : ∀ N : ℕ, |∑ k ∈ range (N + 1), b g k| ≤ 4 * c ^ 2 := by
    intro N
    have := abs_B_le_four_mul_wobblingNorm_sq g ⟨C, hC⟩ N (Nat.cast_nonneg N)
    rwa [B, Nat.floor_natCast] at this
  have key : ∀ n : ℕ, 0 < n → |F n g| ≤ 4 * c ^ 2 * 10 / n := by
    intro n hn
    have hN : (0 : ℝ) < n := by exact_mod_cast hn
    obtain ⟨hs1, -, -, -⟩ := tsum_a_mul_exp_le_three_and_tsum_a_sq_mul_exp_le_inv n hn
    have hsum : Summable (tF_f n g) := by
      refine Summable.of_norm_bounded (hs1.mul_left c) (fun j => ?_)
      have ha0 := tF_a_nonneg n j
      have ha1 := tF_a_le_one n j
      have h1 : a n j ^ 2 / (1 + a n j ^ 2) ≤ a n j := by
        rw [div_le_iff₀ (by positivity)]; nlinarith
      have h2 : abs (abs ((g j : ℤ) : ℝ) - abs ((j : ℤ) : ℝ)) ≤ c :=
        (abs_abs_sub_abs_le_abs_sub _ _).trans (hc j)
      rw [Real.norm_eq_abs, tF_f, abs_mul, abs_mul, abs_of_nonneg (exp_pos _).le,
        abs_of_nonneg (by positivity)]
      have := exp_pos (-(|(j : ℝ)|) / n)
      calc _ ≤ a n j * exp (-(|(j : ℝ)|) / n) * c := by
            gcongr; simpa [Int.cast_abs] using h2
        _ = _ := by ring
    have hF : HasSum (tF_f n g) (F n g) := hsum.hasSum
    have h2 := hF.nat_add_neg.sub (hasSum_ite_eq (0 : ℕ) (tF_f n g 0))
    rw [add_sub_cancel_right] at h2
    have hh : HasSum (fun k : ℕ => tF_psi n k * b g k) (F n g) := by
      have hfun : (fun k : ℕ => tF_psi n k * b g k) = (fun k : ℕ =>
          tF_f n g k + tF_f n g (-k) - if k = 0 then tF_f n g 0 else 0) := by
        funext k
        rcases k with _ | m
        · simp [tF_psi, tF_f, b]
        · have hneg : a n (-((m + 1 : ℕ) : ℤ)) = a n ((m + 1 : ℕ) : ℤ) := by
            simp only [a, Int.cast_neg, abs_neg]
          simp only [tF_psi, tF_f, b, hneg, Nat.add_one_ne_zero, if_false, Int.cast_neg, abs_neg,
            Int.cast_abs, tF_abs_nat]
          ring
      rw [hfun]; exact h2
    have hlim := (hh.tendsto_sum_nat).abs
    refine le_of_tendsto' hlim (fun N => ?_)
    rcases N with _ | m
    · simp; positivity
    · refine (tF_abel_bound (tF_psi n) (b g) (4 * c ^ 2) hB m).trans ?_
      have := tF_var_le n m hn
      calc _ ≤ 4 * c ^ 2 * (10 / n) := mul_le_mul_of_nonneg_left this (by positivity)
        _ = _ := by ring
  refine squeeze_zero_norm' ?_ (tendsto_const_div_atTop_nhds_zero_nat (4 * c ^ 2 * 10))
  filter_upwards [Filter.eventually_gt_atTop 0] with n hn
  rw [Real.norm_eq_abs]
  exact key n hn

end JuschenkoMonod

theorem solution : ∀ (g : Equiv.Perm ℤ) (_ : g ∈ IntervalExchange.wobbling ℤ),
    Filter.Tendsto (fun n => JuschenkoMonod.F n g) Filter.atTop (nhds 0) :=
  fun g hg => JuschenkoMonod.tendsto_F_aux g hg
