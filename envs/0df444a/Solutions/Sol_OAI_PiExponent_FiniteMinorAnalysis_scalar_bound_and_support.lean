-- Prove2me | solution 1 for OAI.PiExponent.FiniteMinorAnalysis.scalar_bound_and_support
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T09:53:05.977775+00:00
-- url     : https://prove2.me/submissions/e46ee85b-a22d-44ad-ba81-b5bba913379b

import Definitions.Def_PiExponent_FiniteTranslationData
import Mathlib

open OAI.PiExponent
open OAI.PiExponent.FiniteMinorAnalysis
open scoped BigOperators

namespace S38SB2

def Good (f : PowerSeries ℂ) : Prop :=
  PowerSeries.coeff 0 f = 0 ∧ ∀ n, ‖PowerSeries.coeff n f‖ ≤ 1

def Bdd (P : PowerSeries ℂ) : Prop := ∀ s, ‖PowerSeries.coeff s P‖ ≤ (2 : ℝ) ^ s

lemma geom_le (s : ℕ) : ∑ k ∈ Finset.range s, (2 : ℝ) ^ k ≤ 2 ^ s := by
  induction s with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, pow_succ]; linarith

lemma bdd_mul {P f : PowerSeries ℂ} (hP : Bdd P) (hf : Good f) : Bdd (P * f) := by
  intro s
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Finset.sum_range_succ]
  simp only [Nat.sub_self, hf.1, mul_zero, add_zero]
  calc ‖∑ k ∈ Finset.range s, PowerSeries.coeff k P * PowerSeries.coeff (s - k) f‖
      ≤ ∑ k ∈ Finset.range s, ‖PowerSeries.coeff k P * PowerSeries.coeff (s - k) f‖ :=
        norm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.range s, (2 : ℝ) ^ k := by
        apply Finset.sum_le_sum; intro k _
        rw [norm_mul]
        calc ‖PowerSeries.coeff k P‖ * ‖PowerSeries.coeff (s - k) f‖ ≤ 2 ^ k * 1 :=
              mul_le_mul (hP k) (hf.2 _) (norm_nonneg _) (by positivity)
          _ = 2 ^ k := mul_one _
    _ ≤ 2 ^ s := geom_le s

lemma bdd_one : Bdd 1 := by
  intro s
  rw [PowerSeries.coeff_one]
  split_ifs with h
  · subst h; simp
  · simp

lemma bdd_mul_pow {P f : PowerSeries ℂ} (hP : Bdd P) (hf : Good f) (n : ℕ) :
    Bdd (P * f ^ n) := by
  induction n with
  | zero => simpa using hP
  | succ n ih => rw [pow_succ, ← mul_assoc]; exact bdd_mul ih hf

lemma bdd_prod {ι : Type*} (s : Finset ι) (f : ι → PowerSeries ℂ) (c : ι → ℕ)
    (hf : ∀ i, Good (f i)) : Bdd (∏ i ∈ s, f i ^ c i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using bdd_one
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, mul_comm]
    exact bdd_mul_pow ih (hf a) (c a)

lemma logTail_good (T : ℕ) : Good (logTail T) := by
  constructor
  · simp [logTail, PowerSeries.coeff_trunc]
  · intro n
    simp only [logTail, map_sub, Polynomial.coeff_coe, PowerSeries.coeff_trunc]
    split_ifs with h
    · simp
    · simp only [zero_sub, norm_neg, PowerSeries.coeff_log]
      split_ifs with h0
      · simp
      · rw [map_div₀, map_pow, map_neg, map_one, map_natCast, norm_div, norm_pow, norm_neg,
          norm_one, one_pow, Complex.norm_natCast]
        have : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr h0
        rw [div_le_one (by linarith)]; exact this

lemma logTail_dvd (T : ℕ) : (PowerSeries.X : PowerSeries ℂ) ^ T ∣ logTail T := by
  rw [PowerSeries.X_pow_dvd_iff]
  intro m hm
  simp [logTail, PowerSeries.coeff_trunc, hm]

lemma coeff_prod_eq_zero {ι : Type*} (s : Finset ι) (T c : ι → ℕ) (n : ℕ)
    (hn : n < ∑ i ∈ s, T i * c i) :
    PowerSeries.coeff n (∏ i ∈ s, logTail (T i) ^ c i) = 0 := by
  have hd : (PowerSeries.X : PowerSeries ℂ) ^ (∑ i ∈ s, T i * c i) ∣
      ∏ i ∈ s, logTail (T i) ^ c i := by
    rw [← Finset.prod_pow_eq_pow_sum]
    apply Finset.prod_dvd_prod_of_dvd
    intro i _
    rw [pow_mul]
    exact pow_dvd_pow_of_dvd (logTail_dvd (T i)) _
  exact (PowerSeries.X_pow_dvd_iff.mp hd) n hn


lemma choose_prod_le {m : ℕ} (a b c : Fin m → ℕ) :
    ((∏ i, (a i).choose (b i) * (a i - b i).choose (c i) : ℕ) : ℝ) ≤
      ∏ i, (4 : ℝ) ^ (a i) := by
  push_cast
  apply Finset.prod_le_prod
  · intro i _; positivity
  · intro i _
    have h1 : ((a i).choose (b i) : ℝ) ≤ 2 ^ (a i) := by
      exact_mod_cast Nat.choose_le_two_pow _ _
    have h2 : ((a i - b i).choose (c i) : ℝ) ≤ 2 ^ (a i) := by
      have := Nat.choose_le_two_pow (a i - b i) (c i)
      have h3 : 2 ^ (a i - b i) ≤ 2 ^ (a i) := Nat.pow_le_pow_right (by norm_num) (Nat.sub_le _ _)
      exact_mod_cast this.trans h3
    calc ((a i).choose (b i) : ℝ) * ((a i - b i).choose (c i) : ℝ) ≤ 2 ^ (a i) * 2 ^ (a i) :=
          mul_le_mul h1 h2 (by positivity) (by positivity)
      _ = 4 ^ (a i) := by rw [← mul_pow]; norm_num

end S38SB2

open S38SB2 in
theorem solution
    {m : ℕ} (K : ℕ) (v theta nu F wmin H : ℝ)
    (p : Fin m → ℤ) (q : Fin m → ℕ)
    (hK : 0 < K) (hv : 0 < v) (htheta : 0 < theta)
    (hnu : 0 ≤ nu) (hF : 0 < F) (hmin : 0 < wmin) (hH : 0 < H)
    (hq : ∀ i, 2 ≤ q i)
    (hwmin : ∀ i, wmin ≤ MatrixArithmetic.logWeights q i)
    (happrox : ∀ i, |Real.pi - (p i : ℝ) / (q i : ℝ)| ≤ (q i : ℝ) ^ (-nu)) :
    ∀ (r : Rows K v theta q H) (t : RowChoice r),
      ‖scalar F p q r t‖ ≤ Real.exp
        (-nu * (weight q t.1.1 - weight q (beta r)) +
          H * translationError K nu F v wmin) ∧
      (scalar F p q r t ≠ 0 → weight q (beta r) ≤ weight q t.1.1) := by
  intro r t
  set w := MatrixArithmetic.logWeights q with hw
  set a : Fin m → ℕ := fun i => t.1.1 i with ha
  set b : Fin m → ℕ := fun i => beta r i with hb
  set c : Fin m → ℕ := fun i => (t.2.1 i : ℕ) with hc
  set s : ℕ := (t.2.2 : ℕ) with hs
  set T := MatrixArithmetic.truncationOrders q F v with hT
  have hw0 : ∀ i, 0 ≤ w i := fun i => by simp only [hw, MatrixArithmetic.logWeights]; positivity
  have hb_eq : ∀ i, b i = r.2.1 i.succ := by
    intro i; simp [hb, beta, InterpolationMatrix.exponentVector]
  -- transverse bound
  have haH : ∑ i, w i * (a i : ℝ) ≤ H := by
    obtain ⟨a', ha'mem, ha'eq⟩ := Finset.mem_map.mp t.1.2
    have h1 := (Finset.mem_filter.mp ha'mem).2
    have : ∀ i, a i = a' i := by
      intro i; simp only [ha, ← ha'eq]; rfl
    simp only [this]; exact h1
  -- row bound
  have hsH : (s : ℝ) * v ≤ H := by
    have hmem := r.2.2
    unfold strictWeightedSimplex at hmem
    have h1 := (Finset.mem_filter.mp hmem).2
    rw [Fin.sum_univ_succ] at h1
    simp only [InterpolationMatrix.rowWeights, Fin.cases_zero, Fin.cases_succ] at h1
    have h2 : 0 ≤ ∑ i : Fin m, w i / theta * (r.2.1 i.succ : ℝ) := by
      apply Finset.sum_nonneg; intro i _
      have := hw0 i; positivity
    have h3 : (s : ℝ) ≤ r.2.1 0 := by
      have := t.2.2.2; exact_mod_cast Nat.lt_succ_iff.mp this
    have : (s : ℝ) * v ≤ v * (r.2.1 0 : ℝ) := by nlinarith
    linarith
  have hsc : scalar F p q r t =
      ((∏ i, (a i).choose (b i) * (a i - b i).choose (c i) : ℕ) : ℂ) *
      (∏ i, ((r.1.val : ℂ) * (MatrixArithmetic.rationalCenters p q i - period)) ^
        (a i - b i - c i)) *
      PowerSeries.coeff s (∏ i, logTail (T i) ^ c i) := rfl
  have hexp_pos := Real.exp_pos (-nu * (weight q t.1.1 - weight q (beta r)) +
          H * translationError K nu F v wmin)
  by_cases hz : scalar F p q r t = 0
  · exact ⟨by rw [hz, norm_zero]; exact hexp_pos.le, fun h => absurd hz h⟩
  have hba : ∀ i, b i ≤ a i := by
    intro i; by_contra hlt; push_neg at hlt
    apply hz; rw [hsc]
    have : (∏ i, (a i).choose (b i) * (a i - b i).choose (c i) : ℕ) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) (by rw [Nat.choose_eq_zero_of_lt hlt, zero_mul])
    rw [this]; simp
  have hsT : ∑ i, T i * c i ≤ s := by
    by_contra hlt; push_neg at hlt
    apply hz; rw [hsc, coeff_prod_eq_zero _ _ _ _ hlt, mul_zero]
  have hca : ∀ i, c i ≤ a i - b i := fun i => Nat.lt_succ_iff.mp (t.2.1 i).2
  have hwt : ∀ x : Fin m →₀ ℕ, weight q x = ∑ i, w i * (x i : ℝ) := fun x => rfl
  refine ⟨?_, fun _ => ?_⟩
  swap
  · rw [hwt, hwt]
    apply Finset.sum_le_sum; intro i _
    apply mul_le_mul_of_nonneg_left _ (hw0 i)
    exact_mod_cast hba i
  -- the norm bound
  set L := Real.log (2 * (K : ℝ)) with hL
  have hK1 : (1 : ℝ) ≤ 2 * (K : ℝ) := by
    have : (1 : ℝ) ≤ K := by exact_mod_cast hK
    linarith
  have hL0 : 0 ≤ L := Real.log_nonneg hK1
  have hfac : ∀ i, ‖(r.1.val : ℂ) * (MatrixArithmetic.rationalCenters p q i - period)‖ ≤
      Real.exp (L + nu - nu * w i) := by
    intro i
    have hq0 : (0 : ℝ) < q i := by have := hq i; positivity
    have heq : (r.1.val : ℂ) * (MatrixArithmetic.rationalCenters p q i - period) =
        (((r.1.val : ℝ) * 2 * ((p i : ℝ) / (q i : ℝ) - Real.pi) : ℝ) : ℂ) * Complex.I := by
      simp only [MatrixArithmetic.rationalCenters, period]
      push_cast; ring
    rw [heq, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_mul, abs_mul]
    have hj : |(r.1.val : ℝ)| ≤ K := by
      rw [abs_of_nonneg (Nat.cast_nonneg _)]; exact_mod_cast r.1.2.le
    have h2 : |((p i : ℝ) / (q i : ℝ) - Real.pi)| ≤ (q i : ℝ) ^ (-nu) := by
      rw [abs_sub_comm]; exact happrox i
    have hwq : w i - 1 ≤ Real.log (q i) := by
      have h0 : 0 ≤ Real.log (q i) := Real.log_nonneg (by exact_mod_cast (by have := hq i; omega : 1 ≤ q i))
      have := Nat.ceil_lt_add_one h0
      simp only [hw, MatrixArithmetic.logWeights]; linarith
    have h3 : (q i : ℝ) ^ (-nu) ≤ Real.exp (nu - nu * w i) := by
      rw [Real.rpow_def_of_pos hq0]
      apply Real.exp_le_exp.mpr
      nlinarith
    calc |(r.1.val : ℝ)| * |(2 : ℝ)| * |((p i : ℝ) / (q i : ℝ) - Real.pi)|
        ≤ K * 2 * Real.exp (nu - nu * w i) := by
          rw [abs_two]
          apply mul_le_mul (mul_le_mul_of_nonneg_right hj (by norm_num)) (h2.trans h3)
            (abs_nonneg _) (by positivity)
      _ = Real.exp (L + nu - nu * w i) := by
          rw [add_sub_assoc, Real.exp_add, hL, Real.exp_log (by linarith)]; ring
  have hcoef : ‖PowerSeries.coeff s (∏ i, logTail (T i) ^ c i)‖ ≤ (2 : ℝ) ^ s :=
    bdd_prod _ _ _ (fun i => logTail_good _) s
  have hpow : ∀ (x : ℝ) (n : ℕ), 0 < x → x ^ n = Real.exp (n * Real.log x) := by
    intro x n hx; rw [Real.exp_nat_mul, Real.exp_log hx]
  have hnorm : ‖scalar F p q r t‖ ≤ Real.exp (
      (∑ i, (a i : ℝ)) * Real.log 4 +
      ∑ i, ((a i - b i - c i : ℕ) : ℝ) * (L + nu - nu * w i) + s * Real.log 2) := by
    rw [hsc, norm_mul, norm_mul, Complex.norm_natCast, norm_prod]
    rw [Real.exp_add, Real.exp_add, Finset.sum_mul, Real.exp_sum, Real.exp_sum]
    apply mul_le_mul _ (hcoef.trans (le_of_eq (hpow 2 s (by norm_num)))) (norm_nonneg _)
      (by positivity)
    apply mul_le_mul _ _ (Finset.prod_nonneg (fun i _ => norm_nonneg _)) (by positivity)
    · refine (choose_prod_le a b c).trans (le_of_eq ?_)
      apply Finset.prod_congr rfl; intro i _
      rw [hpow 4 _ (by norm_num)]
    · apply Finset.prod_le_prod (fun i _ => norm_nonneg _)
      intro i _
      rw [norm_pow, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (norm_nonneg _) (hfac i) _
  refine hnorm.trans (Real.exp_le_exp.mpr ?_)
  -- linear inequality
  have hk : ∀ i, ((a i - b i - c i : ℕ) : ℝ) = (a i : ℝ) - b i - c i := by
    intro i
    rw [Nat.cast_sub (hca i), Nat.cast_sub (hba i)]
  have P1 : (∑ i, (a i : ℝ)) * wmin ≤ H := by
    calc (∑ i, (a i : ℝ)) * wmin = ∑ i, wmin * (a i : ℝ) := by
          rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro i _; ring
      _ ≤ ∑ i, w i * (a i : ℝ) := by
          apply Finset.sum_le_sum; intro i _
          exact mul_le_mul_of_nonneg_right (hwmin i) (Nat.cast_nonneg _)
      _ ≤ H := haH
  have P2 : ∑ i, ((a i - b i - c i : ℕ) : ℝ) ≤ ∑ i, (a i : ℝ) := by
    apply Finset.sum_le_sum; intro i _
    exact_mod_cast Nat.sub_le _ _ |>.trans (Nat.sub_le _ _)
  have P4 : F * ∑ i, w i * (c i : ℝ) ≤ H := by
    have hTi : ∀ i, F * w i ≤ v * T i := by
      intro i
      have := Nat.le_ceil (F * w i / v)
      simp only [hT, MatrixArithmetic.truncationOrders]
      rw [div_le_iff₀ hv] at this; linarith
    calc F * ∑ i, w i * (c i : ℝ) = ∑ i, (F * w i) * (c i : ℝ) := by
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring
      _ ≤ ∑ i, (v * T i) * (c i : ℝ) := by
          apply Finset.sum_le_sum; intro i _
          exact mul_le_mul_of_nonneg_right (hTi i) (Nat.cast_nonneg _)
      _ = v * ((∑ i, T i * c i : ℕ) : ℝ) := by
          push_cast; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring
      _ ≤ v * s := by
          apply mul_le_mul_of_nonneg_left _ hv.le; exact_mod_cast hsT
      _ ≤ H := by linarith
  have hsplit : ∑ i, w i * (a i : ℝ) - ∑ i, w i * (b i : ℝ) =
      ∑ i, ((a i - b i - c i : ℕ) : ℝ) * w i + ∑ i, w i * (c i : ℝ) := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro i _; rw [hk]; ring
  have hsum2 : ∑ i, ((a i - b i - c i : ℕ) : ℝ) * (L + nu - nu * w i) =
      (L + nu) * ∑ i, ((a i - b i - c i : ℕ) : ℝ) - nu * ∑ i, ((a i - b i - c i : ℕ) : ℝ) * w i := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro i _; ring
  rw [hwt, hwt, hsplit, hsum2]
  unfold translationError
  rw [← hL]
  have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have E1 : (∑ i, (a i : ℝ)) * Real.log 4 ≤ H * (Real.log 4 / wmin) := by
    rw [mul_div_assoc', le_div_iff₀ hmin]; nlinarith
  have E2 : (L + nu) * ∑ i, ((a i - b i - c i : ℕ) : ℝ) ≤ H * ((L + nu) / wmin) := by
    rw [mul_div_assoc', le_div_iff₀ hmin]
    have h0 : 0 ≤ L + nu := by linarith
    have h1 : (∑ i, ((a i - b i - c i : ℕ) : ℝ)) * wmin ≤ H :=
      le_trans (mul_le_mul_of_nonneg_right P2 hmin.le) P1
    calc (L + nu) * (∑ i, ((a i - b i - c i : ℕ) : ℝ)) * wmin
        = (L + nu) * ((∑ i, ((a i - b i - c i : ℕ) : ℝ)) * wmin) := by ring
      _ ≤ (L + nu) * H := mul_le_mul_of_nonneg_left h1 h0
      _ = H * (L + nu) := by ring
  have E3 : (s : ℝ) * Real.log 2 ≤ H * (Real.log 2 / v) := by
    rw [mul_div_assoc', le_div_iff₀ hv]; nlinarith
  have E4 : nu * ∑ i, w i * (c i : ℝ) ≤ H * (nu / F) := by
    rw [mul_div_assoc', le_div_iff₀ hF]; nlinarith
  have E5 : H * (nu / F + Real.log 2 / v + (Real.log 4 + L + nu) / wmin) =
      H * (nu / F) + H * (Real.log 2 / v) + H * (Real.log 4 / wmin) + H * ((L + nu) / wmin) := by
    ring
  rw [E5]
  linarith
