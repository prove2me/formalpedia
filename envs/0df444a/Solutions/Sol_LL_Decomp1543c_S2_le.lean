-- Prove2me | solution 1 for LL_Decomp1543c.S2_le
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-04T10:05:27.877018+00:00
-- url     : https://prove2.me/submissions/f3d40082-6afd-4d03-8c88-44ed93d3585f

import Mathlib
import Definitions.Def_LL_Decomp1543c_e
import Definitions.Def_LL_Decomp1543c_nint
import Definitions.Def_LL_Decomp1543c_minK
import Definitions.Def_LL_Decomp1543c_rangeN
import Definitions.Def_LL_Decomp1543c_Ssum
import Definitions.Def_LL_Decomp1543c_lam2

open Real Finset ArithmeticFunction

namespace VaAAux
open LL_Decomp1543c

theorem minK_nonneg (X : ℝ) (hX : 0 ≤ X) (θ : ℝ) : 0 ≤ minK X θ := by
  unfold minK
  split_ifs
  · exact hX
  · exact le_min hX (div_nonneg zero_le_one (mul_nonneg zero_le_two (abs_nonneg _)))

end VaAAux
namespace VaAAux
open LL_Decomp1543c

theorem norm_e (x : ℝ) : ‖e x‖ = 1 := by
  unfold e
  have : (2 * (π : ℂ) * Complex.I * (x : ℂ)) = ((2 * π * x : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [this, Complex.norm_exp_ofReal_mul_I]

theorem e_int (θ : ℝ) (t : ℤ) : e (θ * (t : ℝ)) = (e θ) ^ t := by
  unfold e
  rw [← Complex.exp_int_mul]
  congr 1
  push_cast; ring

theorem e_sub_one_ge (θ : ℝ) : 4 * nint θ ≤ ‖e θ - 1‖ := by
  set s := θ - round θ with hs
  have h1 : e θ = Complex.exp (Complex.I * ((2 * π * s : ℝ) : ℂ)) := by
    unfold e
    have : (2 * (π : ℂ) * Complex.I * (θ : ℂ)) =
        Complex.I * ((2 * π * s : ℝ) : ℂ) + ((round θ : ℤ) : ℂ) * (2 * π * Complex.I) := by
      simp only [hs]; push_cast; ring
    rw [this, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  rw [h1, Complex.norm_exp_I_mul_ofReal_sub_one]
  have h2 : 2 * π * s / 2 = π * s := by ring
  rw [h2]
  have habs : |s| ≤ 1 / 2 := abs_sub_round θ
  have key : 2 * |s| ≤ Real.sin (π * |s|) := by
    have := Real.mul_le_sin (x := π * |s|) (by positivity) (by nlinarith [Real.pi_pos])
    have h3 : 2 / π * (π * |s|) = 2 * |s| := by field_simp
    linarith
  have hfin : 2 * |s| ≤ |Real.sin (π * s)| := by
    rcases le_total 0 s with h | h
    · rw [abs_of_nonneg h] at key ⊢
      have : 0 ≤ Real.sin (π * s) := le_trans (by positivity) key
      rw [abs_of_nonneg this]; exact key
    · rw [abs_of_nonpos h] at key ⊢
      have hsn : Real.sin (π * -s) = - Real.sin (π * s) := by rw [mul_neg, Real.sin_neg]
      rw [hsn] at key
      have : Real.sin (π * s) ≤ 0 := by linarith [le_trans (by linarith : (0:ℝ) ≤ 2 * -s) key]
      rw [abs_of_nonpos this]; linarith
  have h4 : nint θ = |s| := rfl
  rw [Real.norm_eq_abs, abs_mul, abs_two, h4]
  linarith

theorem tel (z : ℂ) (hz : z ≠ 0) (A : ℤ) (n : ℕ) :
    (z - 1) * ∑ t ∈ Ioc A (A + n), z ^ t = z ^ (A + n + 1) - z ^ (A + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hI : Ioc A (A + ((n + 1 : ℕ) : ℤ)) = insert (A + ((n : ℕ) : ℤ) + 1) (Ioc A (A + n)) := by
      ext t; simp only [mem_Ioc, mem_insert]; push_cast; omega
    have hnm : A + ((n : ℕ) : ℤ) + 1 ∉ Ioc A (A + n) := by simp
    rw [hI, sum_insert hnm, mul_add, ih]
    have h5 : A + ((n + 1 : ℕ) : ℤ) + 1 = (A + n + 1) + 1 := by push_cast; ring
    rw [h5, zpow_add_one₀ hz (A + n + 1)]
    ring

theorem geom_gen (θ X : ℝ) (hX : 0 ≤ X) (A B : ℤ) (h : (B : ℝ) - A ≤ X) :
    ‖∑ t ∈ Ioc A B, e (θ * t)‖ ≤ minK X θ := by
  have hX' : ‖∑ t ∈ Ioc A B, e (θ * t)‖ ≤ X := by
    calc ‖∑ t ∈ Ioc A B, e (θ * t)‖ ≤ ∑ t ∈ Ioc A B, ‖e (θ * t)‖ := norm_sum_le _ _
      _ = ((Ioc A B).card : ℝ) := by simp [norm_e]
      _ ≤ X := by
        rw [Int.card_Ioc]
        by_cases hAB : A ≤ B
        · rw [← Int.cast_natCast, Int.toNat_of_nonneg (sub_nonneg.2 hAB)]
          push_cast; exact h
        · have : (B - A).toNat = 0 := Int.toNat_eq_zero.2 (by omega)
          rw [this]; simpa using hX
  unfold minK
  split_ifs with h0
  · exact hX'
  · refine le_min hX' ?_
    have hpos : 0 < nint θ := lt_of_le_of_ne (abs_nonneg _) (Ne.symm h0)
    by_cases hAB : A < B
    · set z := e θ with hzdef
      have hz1 : ‖z‖ = 1 := norm_e θ
      have hz : z ≠ 0 := by intro h0; rw [h0] at hz1; simp at hz1
      have hsum : ∑ t ∈ Ioc A B, e (θ * t) = ∑ t ∈ Ioc A B, z ^ t :=
        sum_congr rfl (fun t _ => e_int θ t)
      have hn : A + (((B - A).toNat : ℕ) : ℤ) = B := by omega
      have htel := tel z hz A (B - A).toNat
      rw [hn] at htel
      have hnorm : ‖z - 1‖ * ‖∑ t ∈ Ioc A B, z ^ t‖ ≤ 2 := by
        rw [← norm_mul, htel]
        calc ‖z ^ (B + 1) - z ^ (A + 1)‖ ≤ ‖z ^ (B + 1)‖ + ‖z ^ (A + 1)‖ := norm_sub_le _ _
          _ = 2 := by simp [norm_zpow, hz1]; norm_num
      have hge := e_sub_one_ge θ
      rw [hsum]
      have hS0 := norm_nonneg (∑ t ∈ Ioc A B, z ^ t)
      rw [le_div_iff₀ (by positivity)]
      nlinarith
    · rw [Ioc_eq_empty hAB]
      simp only [sum_empty, norm_zero]
      positivity
theorem reindex_div (N : ℕ) (R : Finset ℕ) (hR : R ⊆ Icc 1 N) (P : ℕ → Prop) [DecidablePred P]
    (g : ℕ → ℕ → ℂ) :
    ∑ n ∈ R, ∑ t ∈ n.divisors.filter P, g n t =
      ∑ t ∈ (Icc 1 N).filter P, ∑ m ∈ (Icc 1 N).filter (fun m => m * t ∈ R), g (m * t) t := by
  have h : ∀ (n t : ℕ), (n ∈ R ∧ t ∈ n.divisors.filter P) ↔
      (n ∈ R.filter (fun n => t ∣ n) ∧ t ∈ (Icc 1 N).filter P) := by
    intro n t
    simp only [mem_filter, Nat.mem_divisors, mem_Icc]
    constructor
    · rintro ⟨hn, ⟨htn, hn0⟩, hP⟩
      have h1 := mem_Icc.1 (hR hn)
      have h2 := Nat.le_of_dvd (by omega) htn
      exact ⟨⟨hn, htn⟩, ⟨Nat.pos_of_dvd_of_pos htn (by omega), by omega⟩, hP⟩
    · rintro ⟨⟨hn, htn⟩, ⟨ht, hP⟩⟩
      have h1 := mem_Icc.1 (hR hn)
      exact ⟨hn, ⟨htn, by omega⟩, hP⟩
  rw [sum_comm' h]
  apply sum_congr rfl
  intro t ht
  have ht0 : 0 < t := (mem_Icc.1 (mem_filter.1 ht).1).1
  apply sum_nbij' (fun n => n / t) (fun m => m * t)
  · intro n hn
    obtain ⟨hnR, htn⟩ := mem_filter.1 hn
    have h1 := mem_Icc.1 (hR hnR)
    refine mem_filter.2 ⟨mem_Icc.2 ⟨?_, (Nat.div_le_self n t).trans h1.2⟩, ?_⟩
    · exact Nat.div_pos (Nat.le_of_dvd (by omega) htn) ht0
    · rw [Nat.div_mul_cancel htn]; exact hnR
  · intro m hm
    obtain ⟨_, hmR⟩ := mem_filter.1 hm
    exact mem_filter.2 ⟨hmR, dvd_mul_left t m⟩
  · intro n hn
    exact Nat.div_mul_cancel (mem_filter.1 hn).2
  · intro m _
    exact Nat.mul_div_cancel m ht0
  · intro n hn
    rw [Nat.div_mul_cancel (mem_filter.1 hn).2]

theorem geom_nat (θ X : ℝ) (hX : 0 ≤ X) (k l : ℕ) (h : (l : ℝ) - k ≤ X) :
    ‖∑ m ∈ Ioc k l, e (θ * (m : ℝ))‖ ≤ minK X θ := by
  have himg : (Ioc k l).image (Nat.cast : ℕ → ℤ) = Ioc (k : ℤ) (l : ℤ) := by
    ext x
    simp only [mem_image, mem_Ioc]
    constructor
    · rintro ⟨m, hm, rfl⟩
      exact_mod_cast hm
    · rintro ⟨h1, h2⟩
      lift x to ℕ using (by omega)
      refine ⟨x, ?_, rfl⟩
      exact_mod_cast And.intro h1 h2
  have := geom_gen θ X hX k l (by simpa using h)
  rw [← himg, sum_image (fun a _ b _ h => Nat.cast_injective h)] at this
  simpa using this

theorem abel_aux (f : ℕ → ℝ) (hf : Monotone f) (hf0 : ∀ m, 0 ≤ f m) (u : ℕ → ℂ) (K : ℝ) (b : ℕ)
    (hK : ∀ k l : ℕ, k ≤ l → l ≤ b → ‖∑ m ∈ Ioc k l, u m‖ ≤ K) (a : ℕ) :
    ‖∑ m ∈ Ioc a b, (f m : ℂ) * u m‖ ≤ f b * K := by
  have hK0 : 0 ≤ K := by
    have := hK 0 0 le_rfl (Nat.zero_le _)
    simpa using this
  by_cases hab : a < b
  · have key : ∀ d : ℕ, ∀ a : ℕ, a + (d + 1) = b →
        ‖∑ m ∈ Ioc a b, (f m : ℂ) * u m - (f (a + 1) : ℂ) * ∑ m ∈ Ioc a b, u m‖ ≤
          (f b - f (a + 1)) * K := by
      intro d
      induction d with
      | zero =>
        intro a h
        have hb : b = a + 1 := by omega
        subst hb
        simp
      | succ d ih =>
        intro a h
        have hI : Ioc a b = insert (a + 1) (Ioc (a + 1) b) := by
          ext x; simp only [mem_Ioc, mem_insert]; omega
        have hnm : a + 1 ∉ Ioc (a + 1) b := by simp
        have ih' := ih (a + 1) (by omega)
        have hT := hK (a + 1) b (by omega) le_rfl
        have hmon : f (a + 1) ≤ f (a + 1 + 1) := hf (by omega)
        rw [hI, sum_insert hnm, sum_insert hnm]
        have e1 : (f (a + 1) : ℂ) * u (a + 1) + ∑ m ∈ Ioc (a + 1) b, (f m : ℂ) * u m -
            (f (a + 1) : ℂ) * (u (a + 1) + ∑ m ∈ Ioc (a + 1) b, u m) =
            (∑ m ∈ Ioc (a + 1) b, (f m : ℂ) * u m - (f (a + 1 + 1) : ℂ) * ∑ m ∈ Ioc (a + 1) b, u m)
            + (((f (a + 1 + 1) - f (a + 1) : ℝ)) : ℂ) * ∑ m ∈ Ioc (a + 1) b, u m := by
          push_cast; ring
        rw [e1]
        calc _ ≤ ‖∑ m ∈ Ioc (a + 1) b, (f m : ℂ) * u m -
              (f (a + 1 + 1) : ℂ) * ∑ m ∈ Ioc (a + 1) b, u m‖ +
              ‖(((f (a + 1 + 1) - f (a + 1) : ℝ)) : ℂ) * ∑ m ∈ Ioc (a + 1) b, u m‖ :=
              norm_add_le _ _
          _ ≤ (f b - f (a + 1 + 1)) * K + (f (a + 1 + 1) - f (a + 1)) * K := by
              refine add_le_add ih' ?_
              rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
              exact mul_le_mul_of_nonneg_left hT (by linarith)
          _ = (f b - f (a + 1)) * K := by ring
    obtain ⟨d, hd⟩ : ∃ d, a + (d + 1) = b := ⟨b - a - 1, by omega⟩
    have h1 := key d a hd
    have hS := hK a b hab.le le_rfl
    calc ‖∑ m ∈ Ioc a b, (f m : ℂ) * u m‖
        ≤ ‖∑ m ∈ Ioc a b, (f m : ℂ) * u m - (f (a + 1) : ℂ) * ∑ m ∈ Ioc a b, u m‖ +
          ‖(f (a + 1) : ℂ) * ∑ m ∈ Ioc a b, u m‖ := by
          have := norm_add_le
            (∑ m ∈ Ioc a b, (f m : ℂ) * u m - (f (a + 1) : ℂ) * ∑ m ∈ Ioc a b, u m)
            ((f (a + 1) : ℂ) * ∑ m ∈ Ioc a b, u m)
          simpa using this
      _ ≤ (f b - f (a + 1)) * K + f (a + 1) * K := by
          refine add_le_add h1 ?_
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hf0 _)]
          exact mul_le_mul_of_nonneg_left hS (hf0 _)
      _ = f b * K := by ring
  · rw [Ioc_eq_empty hab]
    simp only [sum_empty, norm_zero]
    exact mul_nonneg (hf0 _) hK0

theorem Sk_eq (c : ℝ) (hc : 0 ≤ c) (N k : ℕ) (hk : 1 ≤ k) :
    (Icc 1 N).filter (fun m => m * k ∈ rangeN c N) = Ioc ⌊c * N / k⌋₊ ⌊(N : ℝ) / k⌋₊ := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have h1 : 0 ≤ c * N / k := by positivity
  have h2 : (0 : ℝ) ≤ N / k := by positivity
  ext m
  simp only [mem_filter, mem_Icc, mem_Ioc, rangeN]
  rw [Nat.floor_lt h1, Nat.le_floor_iff h2, div_lt_iff₀ hk', le_div_iff₀ hk']
  push_cast
  constructor
  · rintro ⟨⟨h3, h4⟩, ⟨h5, h6⟩, h7⟩
    have : (m : ℝ) * k ≤ N := by exact_mod_cast h6
    exact ⟨h7, this⟩
  · rintro ⟨h3, h4⟩
    have hm1 : 1 ≤ m := by
      by_contra hm
      have : m = 0 := by omega
      subst this
      simp at h3
      linarith [mul_nonneg hc (Nat.cast_nonneg (α := ℝ) N)]
    have h6 : m * k ≤ N := by exact_mod_cast h4
    have h7 : m ≤ m * k := Nat.le_mul_of_pos_right m hk
    exact ⟨⟨hm1, by omega⟩, ⟨by omega, h6⟩, h3⟩

theorem inner_geom (c : ℝ) (hc : 0 ≤ c) (N : ℕ) (α : ℝ) (k : ℕ) (hk : 1 ≤ k) :
    ‖∑ m ∈ (Icc 1 N).filter (fun m => m * k ∈ rangeN c N), e (α * ((m * k : ℕ) : ℝ))‖ ≤
      minK ((N : ℝ) / k) (α * k) := by
  rw [Sk_eq c hc N k hk]
  have : ∀ m ∈ Ioc ⌊c * N / k⌋₊ ⌊(N : ℝ) / k⌋₊, e (α * ((m * k : ℕ) : ℝ)) =
      e ((α * k) * (m : ℝ)) := by
    intro m _
    congr 1
    push_cast
    ring
  rw [sum_congr rfl this]
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  apply geom_nat _ _ (by positivity)
  calc (⌊(N : ℝ) / k⌋₊ : ℝ) - ⌊c * N / k⌋₊ ≤ ⌊(N : ℝ) / k⌋₊ := sub_le_self _ (Nat.cast_nonneg _)
    _ ≤ N / k := Nat.floor_le (by positivity)

theorem log_mono_nat : Monotone (fun m : ℕ => Real.log (m : ℝ)) := by
  intro m n h
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp only [Nat.cast_zero, Real.log_zero]
    exact Real.log_natCast_nonneg n
  · exact Real.log_le_log (by exact_mod_cast hm) (by exact_mod_cast h)

theorem inner_abel (c : ℝ) (hc : 0 ≤ c) (N : ℕ) (α : ℝ) (k : ℕ) (hk : 1 ≤ k) :
    ‖∑ m ∈ (Icc 1 N).filter (fun m => m * k ∈ rangeN c N),
        ((Real.log m : ℝ) : ℂ) * e (α * ((m * k : ℕ) : ℝ))‖ ≤
      Real.log N * minK ((N : ℝ) / k) (α * k) := by
  rw [Sk_eq c hc N k hk]
  have : ∀ m ∈ Ioc ⌊c * N / k⌋₊ ⌊(N : ℝ) / k⌋₊,
      ((Real.log m : ℝ) : ℂ) * e (α * ((m * k : ℕ) : ℝ)) =
      ((Real.log m : ℝ) : ℂ) * e ((α * k) * (m : ℝ)) := by
    intro m _
    congr 2
    push_cast
    ring
  rw [sum_congr rfl this]
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hbN : ⌊(N : ℝ) / k⌋₊ ≤ N := by
    have h1 : (⌊(N : ℝ) / k⌋₊ : ℝ) ≤ N / k := Nat.floor_le (by positivity)
    have h2 : (N : ℝ) / k ≤ N := div_le_self (Nat.cast_nonneg _) (by exact_mod_cast hk)
    exact_mod_cast h1.trans h2
  have hK : ∀ k' l' : ℕ, k' ≤ l' → l' ≤ ⌊(N : ℝ) / k⌋₊ →
      ‖∑ m ∈ Ioc k' l', e ((α * k) * (m : ℝ))‖ ≤ minK ((N : ℝ) / k) (α * k) := by
    intro k' l' h1 h2
    apply geom_nat _ _ (by positivity)
    have : (l' : ℝ) ≤ ⌊(N : ℝ) / k⌋₊ := by exact_mod_cast h2
    have h3 : (⌊(N : ℝ) / k⌋₊ : ℝ) ≤ N / k := Nat.floor_le (by positivity)
    have : (0 : ℝ) ≤ k' := Nat.cast_nonneg _
    linarith
  have hKnn : 0 ≤ minK ((N : ℝ) / k) (α * k) := by
    have := hK 0 0 le_rfl (Nat.zero_le _)
    simpa using this
  refine (abel_aux (fun m => Real.log (m : ℝ)) log_mono_nat (fun m => Real.log_natCast_nonneg m)
    (fun m => e ((α * k) * (m : ℝ))) _ _ hK _).trans ?_
  exact mul_le_mul_of_nonneg_right (log_mono_nat hbN) hKnn

end VaAAux

open LL_Decomp1543c in
theorem solution (c : ℝ) (hc : 0 ≤ c) (N : ℕ) (V α : ℝ) :
    ‖Ssum (lam2 V) c N α‖ ≤
      Real.log N * ∑ t ∈ Icc 1 ⌊V⌋₊, minK ((N : ℝ) / t) (α * t) := by
  unfold Ssum
  have step : ∀ n ∈ rangeN c N, ((lam2 V n : ℝ) : ℂ) * e (α * n) =
      ∑ t ∈ n.divisors.filter (fun t : ℕ => (t : ℝ) ≤ V),
        (moebius t : ℂ) * ((Real.log ((n / t : ℕ) : ℝ) : ℝ) : ℂ) * e (α * n) := by
    intro n _
    unfold lam2
    push_cast
    rw [sum_mul]
  rw [sum_congr rfl step, VaAAux.reindex_div N (rangeN c N) (filter_subset _ _)
    (fun t : ℕ => (t : ℝ) ≤ V)
    (fun n t => (moebius t : ℂ) * ((Real.log ((n / t : ℕ) : ℝ) : ℝ) : ℂ) * e (α * n))]
  calc _ ≤ ∑ t ∈ (Icc 1 N).filter (fun t : ℕ => (t : ℝ) ≤ V),
        ‖∑ m ∈ (Icc 1 N).filter (fun m => m * t ∈ rangeN c N),
          (moebius t : ℂ) * ((Real.log ((m * t / t : ℕ) : ℝ) : ℝ) : ℂ) *
            e (α * ((m * t : ℕ) : ℝ))‖ :=
        norm_sum_le _ _
    _ ≤ ∑ t ∈ (Icc 1 N).filter (fun t : ℕ => (t : ℝ) ≤ V),
        Real.log N * minK ((N : ℝ) / t) (α * t) := by
        apply sum_le_sum
        intro t ht
        have ht0 : 1 ≤ t := (mem_Icc.1 (mem_filter.1 ht).1).1
        have h1 : ∑ m ∈ (Icc 1 N).filter (fun m => m * t ∈ rangeN c N),
            (moebius t : ℂ) * ((Real.log ((m * t / t : ℕ) : ℝ) : ℝ) : ℂ) *
              e (α * ((m * t : ℕ) : ℝ))
            = (moebius t : ℂ) * ∑ m ∈ (Icc 1 N).filter (fun m => m * t ∈ rangeN c N),
              ((Real.log m : ℝ) : ℂ) * e (α * ((m * t : ℕ) : ℝ)) := by
          rw [mul_sum]
          apply sum_congr rfl
          intro m _
          rw [Nat.mul_div_cancel m ht0, mul_assoc]
        rw [h1, norm_mul]
        have h2 : ‖(moebius t : ℂ)‖ ≤ 1 := by
          rw [Complex.norm_intCast]
          exact_mod_cast abs_moebius_le_one
        calc ‖(moebius t : ℂ)‖ * _ ≤ 1 * (Real.log N * minK ((N : ℝ) / t) (α * t)) :=
            mul_le_mul h2 (VaAAux.inner_abel c hc N α t ht0) (norm_nonneg _) zero_le_one
          _ = _ := one_mul _
    _ ≤ Real.log N * ∑ t ∈ Icc 1 ⌊V⌋₊, minK ((N : ℝ) / t) (α * t) := by
        rw [← mul_sum]
        apply mul_le_mul_of_nonneg_left
        · apply sum_le_sum_of_subset_of_nonneg
          · intro t ht
            obtain ⟨h1, h2⟩ := mem_filter.1 ht
            refine mem_Icc.2 ⟨(mem_Icc.1 h1).1, Nat.le_floor h2⟩
          · intro t _ _
            exact VaAAux.minK_nonneg ((N : ℝ) / t) (by positivity) _
        · exact Real.log_natCast_nonneg N
