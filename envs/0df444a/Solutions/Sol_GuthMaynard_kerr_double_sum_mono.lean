-- Prove2me | solution 1 for GuthMaynard.kerr_double_sum_mono
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-05T22:20:46.548541+00:00
-- url     : https://prove2.me/submissions/2fbf45b1-76d3-43d9-a90a-73a5ed215397

import Mathlib
import Definitions.Def_GuthMaynard

section
open Finset Complex
namespace GuthMaynard.CitedLV.HB
noncomputable section
/-!
# Blueprint: Heath-Brown's large values estimate (Guth–Maynard Theorem 1.6)

Route: B. Kerr, arXiv:1909.12075, §§5–6 (Theorem 16 with `γ` the indicator of a well-spaced set), with
every double sum taken over *all* pairs (the set lies in an interval of length `T`), which makes the
majorant principle exact and removes the Fourier kernels.

`S A N = ∑_{x,y ∈ A} |∑_{N ≤ n ≤ 2N} n^{-1/2} n^{i(x-y)}|²`.

* `majorant`, `completion` (Kerr Lemmas 18, 19);
* `card_divisors_le`, `mono` (Kerr Lemma 20 / Corollary 21: `S(N) ≪ M^ε S(M)` for `M ≥ 64N`),
  `square` (Lemma 22);
* `dyadic_pointwise` (`|∑_{N≤n≤2N} n^{iu}| ≪ N/|u| + |u|^{1/2} log(|u|+2)`), `bprocess` (Kerr Lemma 26,
  van der Corput's B-process: the deep input), `mvt_bound`;
* `dual` (Kerr Lemma 24, 27, Corollary 28), `thm16`, `heath_brown_large_values`.
-/
/-- `∑_{L ≤ n ≤ U} a(n) n^{iu}`. -/
def D (a : ℕ → ℂ) (L U : ℕ) (u : ℝ) : ℂ := ∑ n ∈ Finset.Icc L U, a n * (n : ℂ) ^ ((u : ℂ) * I)

/-- `∑_{x,y ∈ A} |F(x - y)|²`. -/
def Q (A : Finset ℝ) (F : ℝ → ℂ) : ℝ := ∑ x ∈ A, ∑ y ∈ A, ‖F (x - y)‖ ^ 2

/-- The weight `n^{-1/2}`. -/
def w (n : ℕ) : ℂ := (((n : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)

/-- Kerr's `S(N)` over all pairs, unit coefficients. -/
def S (A : Finset ℝ) (N : ℕ) : ℝ := Q A (D w N (2 * N))

end
end GuthMaynard.CitedLV.HB
end

section
open Finset Complex
namespace GuthMaynard.CitedLV.HB.PartM
open GuthMaynard.CitedLV.HB
noncomputable section
/-!
# Part M: the majorant principle and completion

* `Q_expand`: `∑_{x,y}|∑_n c_n n^{i(x-y)}|² = ∑_{n,m} c_n conj(c_m) |∑_x n^{ix} conj(m^{ix})|²`.
* `majorant`: immediate from `Q_expand`.
* `completion`: instead of Fourier completion we use a dyadic (binary) decomposition. With `s = h - L`,
  the prefix `[L, L+s)` telescopes over `k < K` into pieces `[L + s_{k+1}, L + s_k)`, `s_k = ⌊s/2^k⌋ 2^k`,
  each empty or a whole level-`k` dyadic block (offsets `j` with `j / 2^k = m`). Cauchy–Schwarz over
  `k < K` and over the two prefixes gives `|∑_{lo..hi}|² ≤ 4K ∑_{k<K} ∑_m |B_{k,m}|²`, and by `majorant`
  and `Q_expand` the blocks of one level sum to at most `Q A (D |a| L U)`. `K = log₂ U + 1 ≪ 1 + log(U+1)`.
-/
/-- `n^{ix}`. -/
def e (n : ℕ) (x : ℝ) : ℂ := (n : ℂ) ^ ((x : ℂ) * I)

/-- `∑_{x ∈ A} n^{ix} conj(m^{ix})`. -/
def G (A : Finset ℝ) (n m : ℕ) : ℂ := ∑ x ∈ A, e n x * (starRingEnd ℂ) (e m x)

/-- `|G|²`. -/
def g (A : Finset ℝ) (n m : ℕ) : ℝ := ‖G A n m‖ ^ 2

lemma g_nonneg (A : Finset ℝ) (n m : ℕ) : 0 ≤ g A n m := by unfold g; positivity

lemma cpow_sub_eq (n : ℕ) (hn : 1 ≤ n) (x y : ℝ) :
    (n : ℂ) ^ (((x - y : ℝ) : ℂ) * I) = e n x * (starRingEnd ℂ) (e n y) := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  unfold e
  rw [cpow_def_of_ne_zero hn0, cpow_def_of_ne_zero hn0, cpow_def_of_ne_zero hn0, ← Complex.exp_conj,
    ← Complex.exp_add]
  congr 1
  have hlog : Complex.log (n : ℂ) = ((Real.log n : ℝ) : ℂ) := by
    rw [Complex.ofReal_log (by positivity)]; simp
  rw [hlog]
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

lemma swap4 {M : Type*} [AddCommMonoid M] (A : Finset ℝ) (s t : Finset ℕ)
    (f : ℝ → ℝ → ℕ → ℕ → M) :
    ∑ x ∈ A, ∑ y ∈ A, ∑ n ∈ s, ∑ m ∈ t, f x y n m = ∑ n ∈ s, ∑ m ∈ t, ∑ x ∈ A, ∑ y ∈ A, f x y n m := by
  calc _ = ∑ x ∈ A, ∑ n ∈ s, ∑ y ∈ A, ∑ m ∈ t, f x y n m :=
        Finset.sum_congr rfl fun x _ => Finset.sum_comm
    _ = ∑ x ∈ A, ∑ n ∈ s, ∑ m ∈ t, ∑ y ∈ A, f x y n m :=
        Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun n _ => Finset.sum_comm
    _ = ∑ n ∈ s, ∑ x ∈ A, ∑ m ∈ t, ∑ y ∈ A, f x y n m := Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun n _ => Finset.sum_comm

lemma Q_expand (A : Finset ℝ) (L U : ℕ) (hL : 1 ≤ L) (c : ℕ → ℂ) :
    (Q A (D c L U) : ℂ) = ∑ n ∈ Finset.Icc L U, ∑ m ∈ Finset.Icc L U,
      c n * (starRingEnd ℂ) (c m) * ((g A n m : ℝ) : ℂ) := by
  have hterm : ∀ x y : ℝ, ((‖D c L U (x - y)‖ ^ 2 : ℝ) : ℂ) = ∑ n ∈ Finset.Icc L U, ∑ m ∈ Finset.Icc L U,
      c n * (starRingEnd ℂ) (c m) * (e n x * (starRingEnd ℂ) (e m x)) *
        ((starRingEnd ℂ) (e n y) * e m y) := by
    intro x y
    push_cast
    rw [← Complex.mul_conj']
    unfold D
    rw [Finset.sum_congr rfl fun n hn => by
      rw [cpow_sub_eq n (le_trans hL (Finset.mem_Icc.mp hn).1) x y], map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun m _ => ?_
    simp only [map_mul, Complex.conj_conj]
    ring
  unfold Q
  simp only [Complex.ofReal_sum]
  rw [Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => hterm x y, swap4]
  refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun m _ => ?_
  unfold g
  rw [Complex.ofReal_pow, ← Complex.mul_conj']
  unfold G
  rw [map_sum, Finset.sum_mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  simp only [map_mul, Complex.conj_conj]
  ring

lemma Q_real (A : Finset ℝ) (L U : ℕ) (hL : 1 ≤ L) (r : ℕ → ℝ) :
    Q A (D (fun n => ((r n : ℝ) : ℂ)) L U) = ∑ n ∈ Finset.Icc L U, ∑ m ∈ Finset.Icc L U,
      r n * r m * g A n m := by
  have h := Q_expand A L U hL (fun n => ((r n : ℝ) : ℂ))
  simp only [Complex.conj_ofReal] at h
  exact_mod_cast h

theorem majorant (A : Finset ℝ) (L U : ℕ) (hL : 1 ≤ L) (a : ℕ → ℂ) (b : ℕ → ℝ)
    (h : ∀ n ∈ Finset.Icc L U, ‖a n‖ ≤ b n) :
    Q A (D a L U) ≤ Q A (D (fun n => ((b n : ℝ) : ℂ)) L U) := by
  rw [Q_real A L U hL b]
  have h1 : Q A (D a L U) = (Q A (D a L U) : ℂ).re := by simp
  rw [h1, Q_expand A L U hL a]
  calc _ ≤ ‖∑ n ∈ Finset.Icc L U, ∑ m ∈ Finset.Icc L U,
        a n * (starRingEnd ℂ) (a m) * ((g A n m : ℝ) : ℂ)‖ := Complex.re_le_norm _
    _ ≤ ∑ n ∈ Finset.Icc L U, ∑ m ∈ Finset.Icc L U, ‖a n‖ * ‖a m‖ * g A n m := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n _ => ?_)
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun m _ => ?_)
        rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_of_nonneg (g_nonneg _ _ _)]
    _ ≤ _ := by
        refine Finset.sum_le_sum fun n hn => Finset.sum_le_sum fun m hm => ?_
        have := h n hn
        exact mul_le_mul_of_nonneg_right (mul_le_mul (h n hn) (h m hm) (norm_nonneg _)
          (by linarith [norm_nonneg (a n)])) (g_nonneg _ _ _)

end
end GuthMaynard.CitedLV.HB.PartM
end

section
open Finset Complex
namespace GuthMaynard.CitedLV.HB
noncomputable section
/-! ## Part M -/
alias majorant := GuthMaynard.CitedLV.HB.PartM.majorant

end
end GuthMaynard.CitedLV.HB
end

section
open Finset Complex
namespace GuthMaynard.CitedLV.HB.PartM
open GuthMaynard.CitedLV.HB
noncomputable section
/-! ## Completion -/

end
end GuthMaynard.CitedLV.HB.PartM
end

section
open Finset Complex
namespace GuthMaynard.CitedLV.HB
noncomputable section

end
end GuthMaynard.CitedLV.HB
end

section
open Finset Complex
namespace GuthMaynard.CitedLV.HB.PartC
noncomputable section
/-!
# Heath-Brown large values, Part C: `card_divisors_le` and `mono`

* `card_divisors_le`: the divisor bound `τ(n) ≤ C_ε n^ε` (multiplicativity: each prime power
  contributes `(k+1)/p^{kε}`, which is `≤ 1` once `p^ε ≥ 2`).
* `mono` (Kerr Lemma 20 / Corollary 21): `S(N) ≤ C M^ε S(M)` for `M ≥ 64N`. Cut `[N, 2N]` into two
  blocks `[a, b]` with `2b ≤ 3a`. For one block put `U = ⌊M/a⌋ + 1`, `L = ⌊U/8⌋`, `K = L + 1`, and
  average `|D(t) E_ψ(t)|²` over the additive characters `ψ` of `ZMod K`, where
  `E_ψ(t) = ∑_{U ≤ u ≤ U+L} ψ(u) u^{-1/2} u^{it}`. Orthogonality gives
  `∑_ψ |E_ψ(t)|² = K ∑_u 1/u ≥ K/9`; each `D E_ψ` is a Dirichlet polynomial over `[M, 2M]` with
  coefficients bounded by `τ(m) m^{-1/2}`, so `majorant` bounds it by `τmax² S(M)`.
-/
/-! ### The divisor bound -/
/-- `k + 1 ≤ C (p^k)^ε` for all `p ≥ 2`. -/
lemma add_one_le_rpow (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ p : ℕ, 2 ≤ p → ∀ k : ℕ, ((k : ℝ) + 1) ≤ C * (((p ^ k : ℕ) : ℝ)) ^ ε := by
  set c := ε * Real.log 2 with hc
  have hc0 : 0 < c := mul_pos hε (Real.log_pos (by norm_num))
  refine ⟨max 1 (1 / c), le_max_left _ _, fun p hp k => ?_⟩
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  have h1 : 1 + k * c ≤ (((p ^ k : ℕ) : ℝ)) ^ ε := by
    have e1 : (((p ^ k : ℕ) : ℝ)) ^ ε = Real.exp (k * ε * Real.log p) := by
      rw [Real.rpow_def_of_pos (by positivity)]
      push_cast
      rw [Real.log_pow]; ring_nf
    rw [e1]
    have h2 : k * c ≤ k * ε * Real.log p := by
      rw [hc, ← mul_assoc]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Real.log_le_log (by norm_num) (by exact_mod_cast hp)
    linarith [Real.add_one_le_exp (k * ε * Real.log p)]
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  rcases le_total c 1 with hc1 | hc1
  · have : max 1 (1 / c) = 1 / c := max_eq_right (by rw [le_div_iff₀ hc0]; linarith)
    rw [this]
    calc (k : ℝ) + 1 ≤ (1 / c) * (1 + k * c) := by
          have e : (1 / c) * (1 + k * c) = 1 / c + k := by field_simp
          rw [e]
          have : 1 ≤ 1 / c := by rw [le_div_iff₀ hc0]; linarith
          linarith
      _ ≤ (1 / c) * (((p ^ k : ℕ) : ℝ)) ^ ε := mul_le_mul_of_nonneg_left h1 (by positivity)
  · have : max 1 (1 / c) = 1 := max_eq_left (by rw [div_le_iff₀ hc0]; linarith)
    rw [this, one_mul]
    have : (k : ℝ) ≤ k * c := le_mul_of_one_le_right hk0 hc1
    linarith

/-- The divisor bound `τ(n) ≤ C n^ε`. -/
theorem tau_le_rpow (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, n ≠ 0 → (n.divisors.card : ℝ) ≤ C * (n : ℝ) ^ ε := by
  classical
  obtain ⟨C₀, hC₀1, hC₀⟩ := add_one_le_rpow ε hε
  set N := ⌈(2 : ℝ) ^ (1 / ε)⌉₊ + 1 with hN
  set Ssmall := (Finset.range N).filter (fun p : ℕ => ¬ (2 ≤ (p : ℝ) ^ ε)) with hS
  refine ⟨C₀ ^ Ssmall.card, by positivity, fun n hn => ?_⟩
  have hmemS : ∀ p : ℕ, 2 ≤ p → ¬ (2 ≤ (p : ℝ) ^ ε) → p ∈ Ssmall := by
    intro p hp2 hlt
    have hp0 : (0 : ℝ) ≤ (p : ℝ) := by positivity
    have hlt' : (p : ℝ) ^ ε < 2 := lt_of_not_ge hlt
    have h1 : ((p : ℝ) ^ ε) ^ (1 / ε) = (p : ℝ) := by
      rw [← Real.rpow_mul hp0, mul_one_div, div_self hε.ne', Real.rpow_one]
    have h2 : ((p : ℝ) ^ ε) ^ (1 / ε) < (2 : ℝ) ^ (1 / ε) :=
      Real.rpow_lt_rpow (by positivity) hlt' (by positivity)
    rw [h1] at h2
    have h3 : (p : ℝ) < (⌈(2 : ℝ) ^ (1 / ε)⌉₊ : ℝ) := lt_of_lt_of_le h2 (Nat.le_ceil _)
    have h4 : p < N := by
      have : p < ⌈(2 : ℝ) ^ (1 / ε)⌉₊ := by exact_mod_cast h3
      omega
    rw [hS, Finset.mem_filter, Finset.mem_range]
    exact ⟨h4, hlt⟩
  rw [Nat.card_divisors hn]
  push_cast
  have hfac : ∀ p ∈ n.primeFactors, ((n.factorization p : ℝ) + 1)
      ≤ (if p ∈ Ssmall then C₀ else 1) * (((p ^ n.factorization p : ℕ)) : ℝ) ^ ε := by
    intro p hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hp2 : 2 ≤ p := hpp.two_le
    by_cases hsm : 2 ≤ (p : ℝ) ^ ε
    · have hnot : p ∉ Ssmall := by simp [hS, hsm]
      rw [if_neg hnot, one_mul]
      set k := n.factorization p
      have hpk : (((p ^ k : ℕ)) : ℝ) ^ ε = ((p : ℝ) ^ ε) ^ k := by
        push_cast
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity), mul_comm,
          Real.rpow_mul (by positivity), Real.rpow_natCast]
      rw [hpk]
      have h2k : (k : ℝ) + 1 ≤ 2 ^ k := by
        have : k + 1 ≤ 2 ^ k := Nat.lt_two_pow_self
        exact_mod_cast this
      exact h2k.trans (pow_le_pow_left₀ (by norm_num) hsm k)
    · rw [if_pos (hmemS p hp2 hsm)]
      exact hC₀ p hp2 _
  have hconst : (∏ p ∈ n.primeFactors, (if p ∈ Ssmall then C₀ else 1)) ≤ C₀ ^ Ssmall.card := by
    rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]
    refine pow_le_pow_right₀ hC₀1 ?_
    exact Finset.card_le_card fun x hx => (Finset.mem_filter.1 hx).2
  have hprod_n : (∏ p ∈ n.primeFactors, (((p ^ n.factorization p : ℕ)) : ℝ)) = (n : ℝ) := by
    rw [← Nat.cast_prod]
    exact congrArg _ (Nat.prod_primeFactors_pow_factorization hn).symm
  have hrpow : (∏ p ∈ n.primeFactors, (((p ^ n.factorization p : ℕ)) : ℝ) ^ ε) = (n : ℝ) ^ ε := by
    rw [Real.finsetProd_rpow _ _ (fun p _ => by positivity) ε, hprod_n]
  calc ∏ p ∈ n.primeFactors, ((n.factorization p : ℝ) + 1)
      ≤ ∏ p ∈ n.primeFactors,
          ((if p ∈ Ssmall then C₀ else 1) * (((p ^ n.factorization p : ℕ)) : ℝ) ^ ε) :=
        Finset.prod_le_prod (fun p _ => by positivity) hfac
    _ = (∏ p ∈ n.primeFactors, (if p ∈ Ssmall then C₀ else 1)) *
          (∏ p ∈ n.primeFactors, (((p ^ n.factorization p : ℕ)) : ℝ) ^ ε) :=
        Finset.prod_mul_distrib
    _ ≤ C₀ ^ Ssmall.card * (n : ℝ) ^ ε := by
        rw [hrpow]; exact mul_le_mul_of_nonneg_right hconst (by positivity)

end
end GuthMaynard.CitedLV.HB.PartC
end

section
open Finset Complex
namespace GuthMaynard.CitedLV.HB
noncomputable section
/-! ## Part C -/

end
end GuthMaynard.CitedLV.HB
end

section
open Finset Complex
namespace GuthMaynard.CitedLV.HB.PartC
noncomputable section
/-! ### Elementary facts -/
/-- `u^{-1/2}`. -/
def r (u : ℕ) : ℝ := (u : ℝ) ^ (-(1 / 2 : ℝ))

lemma r_nonneg (u : ℕ) : 0 ≤ r u := Real.rpow_nonneg (Nat.cast_nonneg u) _

lemma r_sq {u : ℕ} (_hu : 1 ≤ u) : r u ^ 2 = 1 / (u : ℝ) := by
  have h0 : (0 : ℝ) ≤ u := Nat.cast_nonneg u
  unfold r
  rw [← Real.rpow_natCast, ← Real.rpow_mul h0]
  norm_num
  rw [Real.rpow_neg_one, inv_eq_one_div]

lemma r_mul (n u : ℕ) : r n * r u = r (n * u) := by
  unfold r; push_cast; rw [Real.mul_rpow (Nat.cast_nonneg n) (Nat.cast_nonneg u)]

lemma norm_cpow_I {n : ℕ} (hn : 1 ≤ n) (t : ℝ) : ‖(n : ℂ) ^ ((t : ℂ) * I)‖ = 1 := by
  rw [Complex.norm_natCast_cpow_of_pos (by omega)]; simp

lemma Q_nonneg (A : Finset ℝ) (F : ℝ → ℂ) : 0 ≤ Q A F := by
  unfold Q; positivity

lemma Q_smul (A : Finset ℝ) (F : ℝ → ℂ) (z : ℂ) :
    Q A (fun t => z * F t) = ‖z‖ ^ 2 * Q A F := by
  unfold Q; simp [mul_pow, Finset.mul_sum]

lemma Q_add_le (A : Finset ℝ) (F G : ℝ → ℂ) :
    Q A (fun t => F t + G t) ≤ 2 * Q A F + 2 * Q A G := by
  unfold Q
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun x _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun y _ => ?_
  have h := norm_add_le (F (x - y)) (G (x - y))
  have h0 : 0 ≤ ‖F (x - y) + G (x - y)‖ := norm_nonneg _
  nlinarith [sq_nonneg (‖F (x - y)‖ - ‖G (x - y)‖), norm_nonneg (F (x - y)),
    norm_nonneg (G (x - y))]

/-! ### The character sums -/
/-- `E_ψ(t) = ∑_{u ∈ Us} ψ(u) u^{-1/2} u^{it}`. -/
def E (K : ℕ) [NeZero K] (Us : Finset ℕ) (ψ : AddChar (ZMod K) ℂ) (t : ℝ) : ℂ :=
  ∑ u ∈ Us, ψ (u : ZMod K) * ((r u : ℝ) : ℂ) * (u : ℂ) ^ ((t : ℂ) * I)

lemma sum_E_mul_conj (K : ℕ) [NeZero K] (Us : Finset ℕ) (hpos : ∀ u ∈ Us, 1 ≤ u)
    (hinj : ∀ u₁ ∈ Us, ∀ u₂ ∈ Us, (u₁ : ZMod K) = u₂ → u₁ = u₂) (t : ℝ) :
    ∑ ψ : AddChar (ZMod K) ℂ, E K Us ψ t * (starRingEnd ℂ) (E K Us ψ t)
      = (K : ℂ) * ∑ u ∈ Us, ((1 / (u : ℝ) : ℝ) : ℂ) := by
  classical
  set g : ℕ → ℂ := fun u => ((r u : ℝ) : ℂ) * (u : ℂ) ^ ((t : ℂ) * I) with hg
  have h1 : ∀ ψ : AddChar (ZMod K) ℂ, E K Us ψ t * (starRingEnd ℂ) (E K Us ψ t)
      = ∑ u₁ ∈ Us, ∑ u₂ ∈ Us, ψ ((u₁ : ZMod K) - u₂) * (g u₁ * (starRingEnd ℂ) (g u₂)) := by
    intro ψ
    unfold E
    rw [map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun u₁ _ => Finset.sum_congr rfl fun u₂ _ => ?_
    rw [sub_eq_add_neg, AddChar.map_add_eq_mul, AddChar.map_neg_eq_conj]
    simp only [hg, map_mul]
    ring
  simp_rw [h1]
  rw [Finset.sum_comm]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun u₁ hu₁ => ?_
  rw [Finset.sum_comm]
  rw [Finset.sum_eq_single u₁]
  · rw [← Finset.sum_mul, AddChar.sum_apply_eq_ite, sub_self, if_pos rfl, ZMod.card]
    congr 1
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    have hn : ‖g u₁‖ = r u₁ := by
      simp only [hg, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (r_nonneg _),
        norm_cpow_I (hpos u₁ hu₁), mul_one]
    rw [hn, r_sq (hpos u₁ hu₁)]
  · intro u₂ hu₂ hne
    rw [← Finset.sum_mul, AddChar.sum_apply_eq_ite, if_neg, zero_mul]
    intro h
    exact hne (hinj u₂ hu₂ u₁ hu₁ (sub_eq_zero.mp h).symm)
  · intro h; exact absurd hu₁ h

lemma sum_norm_E_sq (K : ℕ) [NeZero K] (Us : Finset ℕ) (hpos : ∀ u ∈ Us, 1 ≤ u)
    (hinj : ∀ u₁ ∈ Us, ∀ u₂ ∈ Us, (u₁ : ZMod K) = u₂ → u₁ = u₂) (t : ℝ) :
    ∑ ψ : AddChar (ZMod K) ℂ, ‖E K Us ψ t‖ ^ 2 = (K : ℝ) * ∑ u ∈ Us, 1 / (u : ℝ) := by
  have h := sum_E_mul_conj K Us hpos hinj t
  have h2 : ∀ ψ : AddChar (ZMod K) ℂ, E K Us ψ t * (starRingEnd ℂ) (E K Us ψ t)
      = ((‖E K Us ψ t‖ ^ 2 : ℝ) : ℂ) := by
    intro ψ; rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  simp_rw [h2] at h
  exact_mod_cast h

/-- The averaged identity: `∑_ψ Q(D E_ψ) = K (∑ 1/u) Q(D)`. -/
lemma sum_Q_mul_E (A : Finset ℝ) (F : ℝ → ℂ) (K : ℕ) [NeZero K] (Us : Finset ℕ)
    (hpos : ∀ u ∈ Us, 1 ≤ u)
    (hinj : ∀ u₁ ∈ Us, ∀ u₂ ∈ Us, (u₁ : ZMod K) = u₂ → u₁ = u₂) :
    ∑ ψ : AddChar (ZMod K) ℂ, Q A (fun t => F t * E K Us ψ t)
      = (K : ℝ) * (∑ u ∈ Us, 1 / (u : ℝ)) * Q A F := by
  unfold Q
  simp_rw [norm_mul, mul_pow]
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [← Finset.mul_sum, sum_norm_E_sq K Us hpos hinj]
  ring

/-! ### The product polynomial -/
/-- Coefficients of `D(w on [a,b]) · E_ψ`. -/
def c (K : ℕ) [NeZero K] (ψ : AddChar (ZMod K) ℂ) (a b : ℕ) (Us : Finset ℕ) (m : ℕ) : ℂ :=
  ∑ p ∈ Icc a b ×ˢ Us with p.1 * p.2 = m, w p.1 * (ψ (p.2 : ZMod K) * ((r p.2 : ℝ) : ℂ))

lemma D_mul_E (K : ℕ) [NeZero K] (ψ : AddChar (ZMod K) ℂ) (a b M : ℕ) (Us : Finset ℕ)
    (hmap : ∀ n ∈ Icc a b, ∀ u ∈ Us, n * u ∈ Icc M (2 * M)) (t : ℝ) :
    D w a b t * E K Us ψ t = D (c K ψ a b Us) M (2 * M) t := by
  have lhs : D w a b t * E K Us ψ t = ∑ p ∈ Icc a b ×ˢ Us,
      w p.1 * (ψ (p.2 : ZMod K) * ((r p.2 : ℝ) : ℂ)) * ((p.1 * p.2 : ℕ) : ℂ) ^ ((t : ℂ) * I) := by
    unfold D E
    rw [Finset.sum_mul_sum, Finset.sum_product]
    refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun u _ => ?_
    push_cast
    rw [natCast_mul_natCast_cpow]
    ring
  have hmap' : ∀ p ∈ Icc a b ×ˢ Us, (fun p : ℕ × ℕ => p.1 * p.2) p ∈ Icc M (2 * M) := by
    intro p hp
    rw [Finset.mem_product] at hp
    exact hmap p.1 hp.1 p.2 hp.2
  rw [lhs, ← Finset.sum_fiberwise_of_maps_to hmap']
  unfold D c
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [(Finset.mem_filter.1 hp).2]

lemma norm_c_le (K : ℕ) [NeZero K] (ψ : AddChar (ZMod K) ℂ) (a b : ℕ) (Us : Finset ℕ)
    (ha : 1 ≤ a) (m : ℕ) (hm : 1 ≤ m) (T : ℝ) (hT : (m.divisors.card : ℝ) ≤ T) :
    ‖c K ψ a b Us m‖ ≤ T * r m := by
  classical
  unfold c
  set F := (Icc a b ×ˢ Us).filter (fun p : ℕ × ℕ => p.1 * p.2 = m) with hF
  have hterm : ∀ p ∈ F, ‖w p.1 * (ψ (p.2 : ZMod K) * ((r p.2 : ℝ) : ℂ))‖ = r m := by
    intro p hp
    have hpm : p.1 * p.2 = m := (Finset.mem_filter.1 hp).2
    rw [norm_mul, norm_mul, AddChar.norm_apply, one_mul]
    rw [show w p.1 = ((r p.1 : ℝ) : ℂ) from rfl]
    rw [Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
    rw [abs_of_nonneg (r_nonneg _), abs_of_nonneg (r_nonneg _), ← hpm]
    exact r_mul p.1 p.2
  have hcard : F.card ≤ m.divisors.card := by
    apply Finset.card_le_card_of_injOn (fun p : ℕ × ℕ => p.1)
    · intro p hp
      have hp' := Finset.mem_filter.1 hp
      simp only [Finset.mem_coe, Nat.mem_divisors]
      exact ⟨⟨p.2, hp'.2.symm⟩, by omega⟩
    · intro p hp q hq hpq
      have hp' := Finset.mem_filter.1 hp
      have hq' := Finset.mem_filter.1 hq
      have hp1 : a ≤ p.1 := (Finset.mem_Icc.1 (Finset.mem_product.1 hp'.1).1).1
      simp only at hpq
      have h2 : p.2 = q.2 := by
        apply Nat.eq_of_mul_eq_mul_left (show 0 < p.1 by omega)
        rw [hp'.2, hpq, hq'.2]
      exact Prod.ext hpq h2
  calc ‖∑ p ∈ F, w p.1 * (ψ (p.2 : ZMod K) * ((r p.2 : ℝ) : ℂ))‖
      ≤ ∑ p ∈ F, ‖w p.1 * (ψ (p.2 : ZMod K) * ((r p.2 : ℝ) : ℂ))‖ := norm_sum_le _ _
    _ = ∑ p ∈ F, r m := Finset.sum_congr rfl hterm
    _ = F.card * r m := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ T * r m := by
        apply mul_le_mul_of_nonneg_right _ (r_nonneg _)
        exact le_trans (by exact_mod_cast hcard) hT

lemma Q_D_c_le (A : Finset ℝ) (K : ℕ) [NeZero K] (ψ : AddChar (ZMod K) ℂ) (a b M : ℕ)
    (Us : Finset ℕ) (ha : 1 ≤ a) (hM : 1 ≤ M) (T : ℝ)
    (hT : ∀ m ∈ Icc M (2 * M), (m.divisors.card : ℝ) ≤ T) :
    Q A (D (c K ψ a b Us) M (2 * M)) ≤ T ^ 2 * S A M := by
  have h := GuthMaynard.CitedLV.HB.majorant A M (2 * M) hM (c K ψ a b Us) (fun m => T * r m)
    (fun m hm => norm_c_le K ψ a b Us ha m (by have := (Finset.mem_Icc.1 hm).1; omega) T
      (hT m hm))
  have e : D (fun m => (((T * r m : ℝ)) : ℂ)) M (2 * M) = fun t => (T : ℂ) * D w M (2 * M) t := by
    funext t
    unfold D w r
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    push_cast
    ring
  rw [e, Q_smul, Complex.norm_real, Real.norm_eq_abs, sq_abs] at h
  exact h

/-! ### One block -/
lemma inv_sum_ge (U L : ℕ) (hU : 1 ≤ U) (hL : U ≤ 8 * L + 7) :
    (1 / 9 : ℝ) ≤ ∑ u ∈ Icc U (U + L), 1 / (u : ℝ) := by
  have h : ∀ u ∈ Icc U (U + L), 1 / ((U + L : ℕ) : ℝ) ≤ 1 / (u : ℝ) := by
    intro u hu
    have hu' := Finset.mem_Icc.1 hu
    apply one_div_le_one_div_of_le (by exact_mod_cast (by omega : 0 < u))
    exact_mod_cast hu'.2
  have h2 := Finset.card_nsmul_le_sum _ _ _ h
  rw [Nat.card_Icc, nsmul_eq_mul] at h2
  refine le_trans ?_ h2
  have hpos : (0 : ℝ) < ((U + L : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < U + L)
  rw [mul_one_div, le_div_iff₀ hpos]
  have : ((U + L : ℕ) : ℝ) ≤ 9 * ((U + L + 1 - U : ℕ) : ℝ) := by
    exact_mod_cast (by omega : U + L ≤ 9 * (U + L + 1 - U))
  linarith

lemma block (A : Finset ℝ) (a b M : ℕ) (ha : 1 ≤ a) (hab : 2 * b ≤ 3 * a) (haM : 32 * a ≤ M)
    (T : ℝ) (hT : ∀ m ∈ Icc M (2 * M), (m.divisors.card : ℝ) ≤ T) :
    Q A (D w a b) ≤ 9 * T ^ 2 * S A M := by
  obtain ⟨U, hU⟩ : ∃ U, U = M / a + 1 := ⟨_, rfl⟩
  obtain ⟨L, hL⟩ : ∃ L, L = U / 8 := ⟨_, rfl⟩
  set K := L + 1 with hK
  set Us := Icc U (U + L) with hUs
  have hM : 1 ≤ M := by omega
  have hUa1 : M ≤ U * a := by
    have := Nat.div_add_mod M a
    have := Nat.mod_lt M (show 0 < a by omega)
    rw [hU, Nat.add_mul, one_mul, mul_comm]; omega
  have hUa2 : U * a ≤ M + a := by
    have := Nat.div_mul_le_self M a
    rw [hU, Nat.add_mul, one_mul]; omega
  have h8L : 8 * L ≤ U := by rw [hL]; exact Nat.mul_div_le U 8
  have h8L' : U ≤ 8 * L + 7 := by rw [hL]; omega
  have hU1 : 1 ≤ U := by rw [hU]; exact Nat.le_add_left 1 _
  have hpos : ∀ u ∈ Us, 1 ≤ u := by
    intro u hu; have := (Finset.mem_Icc.1 hu).1; omega
  have hinj : ∀ u₁ ∈ Us, ∀ u₂ ∈ Us, (u₁ : ZMod K) = u₂ → u₁ = u₂ := by
    intro u₁ h₁ u₂ h₂ he
    have h₁' := Finset.mem_Icc.1 h₁
    have h₂' := Finset.mem_Icc.1 h₂
    rw [ZMod.natCast_eq_natCast_iff] at he
    rcases le_total u₁ u₂ with h | h
    · have hd := (Nat.modEq_iff_dvd' h).1 he
      have : u₂ - u₁ = 0 := Nat.eq_zero_of_dvd_of_lt hd (by omega)
      omega
    · have hd := (Nat.modEq_iff_dvd' h).1 he.symm
      have : u₁ - u₂ = 0 := Nat.eq_zero_of_dvd_of_lt hd (by omega)
      omega
  have hmap : ∀ n ∈ Icc a b, ∀ u ∈ Us, n * u ∈ Icc M (2 * M) := by
    intro n hn u hu
    have hn' := Finset.mem_Icc.1 hn
    have hu' := Finset.mem_Icc.1 hu
    rw [Finset.mem_Icc]
    constructor
    · calc M ≤ U * a := hUa1
        _ ≤ u * n := Nat.mul_le_mul hu'.1 hn'.1
        _ = n * u := mul_comm _ _
    · have h1 : n * u ≤ b * (U + L) := Nat.mul_le_mul hn'.2 hu'.2
      have h2 : 16 * (b * (U + L)) ≤ 9 * (U * (2 * b)) := by
        have := Nat.mul_le_mul_left (2 * b) h8L
        nlinarith
      have h3 : U * (2 * b) ≤ U * (3 * a) := Nat.mul_le_mul_left U hab
      have h4 : U * (3 * a) ≤ 3 * (M + a) := by nlinarith
      omega
  have hid := sum_Q_mul_E A (D w a b) K Us hpos hinj
  have hle : ∑ ψ : AddChar (ZMod K) ℂ, Q A (fun t => D w a b t * E K Us ψ t)
      ≤ (K : ℝ) * (T ^ 2 * S A M) := by
    have : ∀ ψ : AddChar (ZMod K) ℂ, Q A (fun t => D w a b t * E K Us ψ t) ≤ T ^ 2 * S A M := by
      intro ψ
      have e : (fun t => D w a b t * E K Us ψ t) = D (c K ψ a b Us) M (2 * M) := by
        funext t; exact D_mul_E K ψ a b M Us hmap t
      rw [e]
      exact Q_D_c_le A K ψ a b M Us ha hM T hT
    calc _ ≤ ∑ _ψ : AddChar (ZMod K) ℂ, T ^ 2 * S A M := Finset.sum_le_sum fun ψ _ => this ψ
      _ = (K : ℝ) * (T ^ 2 * S A M) := by
        rw [Finset.sum_const, Finset.card_univ, AddChar.card_eq, ZMod.card, nsmul_eq_mul]
  rw [hid] at hle
  have hK0 : (0 : ℝ) < K := by exact_mod_cast (by omega : 0 < K)
  have hs := inv_sum_ge U L hU1 h8L'
  have hQ := Q_nonneg A (D w a b)
  have h1 : (∑ u ∈ Us, 1 / (u : ℝ)) * Q A (D w a b) ≤ T ^ 2 * S A M := by
    rw [mul_assoc] at hle
    exact le_of_mul_le_mul_left hle hK0
  nlinarith

/-! ### `mono` -/
lemma split (A : Finset ℝ) (N : ℕ) :
    S A N ≤ 2 * Q A (D w N (3 * N / 2)) + 2 * Q A (D w (3 * N / 2 + 1) (2 * N)) := by
  have e : D w N (2 * N) = fun t => D w N (3 * N / 2) t + D w (3 * N / 2 + 1) (2 * N) t := by
    funext t
    unfold D
    rw [← Finset.sum_union]
    · congr 1
      ext n; simp only [Finset.mem_Icc, Finset.mem_union]; omega
    · rw [Finset.disjoint_left]
      intro n h1 h2
      simp only [Finset.mem_Icc] at h1 h2
      omega
  unfold S
  rw [e]
  exact Q_add_le A _ _

theorem mono : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ (A : Finset ℝ) (N M : ℕ), 1 ≤ N →
    64 * N ≤ M → S A N ≤ C * (M : ℝ) ^ ε * S A M := by
  intro ε hε
  obtain ⟨C₀, hC₀, hτ⟩ := tau_le_rpow (ε / 2) (by linarith)
  refine ⟨36 * C₀ ^ 2 * 2 ^ ε, by positivity, fun A N M hN hNM => ?_⟩
  set T := C₀ * (2 * (M : ℝ)) ^ (ε / 2) with hTdef
  have hT : ∀ m ∈ Icc M (2 * M), (m.divisors.card : ℝ) ≤ T := by
    intro m hm
    have hm' := Finset.mem_Icc.1 hm
    refine le_trans (hτ m (by omega)) ?_
    apply mul_le_mul_of_nonneg_left _ hC₀.le
    apply Real.rpow_le_rpow (Nat.cast_nonneg m) _ (by linarith)
    exact_mod_cast hm'.2
  have hT2 : T ^ 2 = C₀ ^ 2 * 2 ^ ε * (M : ℝ) ^ ε := by
    have e : ((2 * (M : ℝ)) ^ (ε / 2)) ^ 2 = (2 * (M : ℝ)) ^ ε := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
      norm_num
    rw [hTdef, mul_pow, e, Real.mul_rpow (by norm_num) (Nat.cast_nonneg M)]
    ring
  have hb1 := block A N (3 * N / 2) M (by omega) (by omega) (by omega) T hT
  have hb2 := block A (3 * N / 2 + 1) (2 * N) M (by omega) (by omega) (by omega) T hT
  have hsp := split A N
  have : S A N ≤ 36 * T ^ 2 * S A M := by linarith
  rw [hT2] at this
  linarith

end
end GuthMaynard.CitedLV.HB.PartC
end

section
open Finset Complex
namespace GuthMaynard.CitedLV.HB
noncomputable section
alias mono := GuthMaynard.CitedLV.HB.PartC.mono

/-! ## Part Q -/

/-! ## Part P -/

/-! ## Part D -/

/-! ## Part T -/

end
end GuthMaynard.CitedLV.HB
end


open GuthMaynard in
theorem solution : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ (A : Finset ℝ) (N M : ℕ), 1 ≤ N →
    64 * N ≤ M →
    (∑ x ∈ A, ∑ y ∈ A, ‖∑ n ∈ Finset.Icc N (2 * N), (((n : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * (n : ℂ) ^ (((x - y : ℝ) : ℂ) * Complex.I)‖ ^ 2) ≤
      C * (M : ℝ) ^ ε * (∑ x ∈ A, ∑ y ∈ A, ‖∑ n ∈ Finset.Icc M (2 * M), (((n : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * (n : ℂ) ^ (((x - y : ℝ) : ℂ) * Complex.I)‖ ^ 2) :=
  GuthMaynard.CitedLV.HB.mono
