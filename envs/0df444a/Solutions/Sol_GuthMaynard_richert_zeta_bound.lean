-- Prove2me | solution 1 for GuthMaynard.richert_zeta_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T19:43:19.049654+00:00
-- url     : https://prove2.me/submissions/2afc9bc3-8238-4feb-ac01-189455ba7499
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_GuthMaynard_ford_exponential_sum_bound
import Theorems.Thm_Zeta0EqZeta
import Theorems.Thm_ExponentialSums_kusmin_landau

section
open Complex Filter Topology Set
namespace GuthMaynard.CitedZeros.Rich
/-!
# Richert's bound `|ζ(σ+it)| ≤ A|t|^{B(1-σ)^{3/2}} log^{2/3}|t|`: blueprint

Ford, *Vinogradov's integral and bounds for the Riemann zeta function* (arXiv:1910.08209v1), §7,
Lemma 7.3 (pp. 66–67), with its input `GuthMaynard.ford_exponential_sum_bound` (Ford's Theorem 2).
Ford's Lemmas 7.1–7.2 (the crude bound and the approximate formula for `σ ≥ 15/16`) are replaced by
* `Zeta0EqZeta` (Euler–Maclaurin: `ζ = ∑_{n ≤ N} n^{-s} - N^{1-s}/(1-s) - N^{-s}/2 + s∫_N^∞ …`)
  with `N ≈ t²`, so that all the error terms are `O(1)` for `1/2 ≤ σ ≤ 1`;
* `ExponentialSums.kusmin_landau` for the blocks `t < n ≤ t²` (phase derivative `t/(2πn) ≤ 1/(2π)`);
so the dyadic argument of Lemma 7.3 runs for all `1/2 ≤ σ ≤ 1` and `t` large; small `|t|` is
compactness, negative `t` conjugation.

Every lemma marked `sorry` is a prover target; the assembly `richert_zeta_bound_dev` is sorry-free
modulo them.
-/
/-- The dyadic exponent `g(j) = (1-σ) j log 2 - (j log 2)^3 / (133.66 log² t)` (Ford, p. 67). -/
noncomputable def gexp (σ L : ℝ) (j : ℕ) : ℝ :=
  (1 - σ) * (j * Real.log 2) - (j * Real.log 2) ^ 3 / (133.66 * L ^ 2)

end GuthMaynard.CitedZeros.Rich
end

section
open Complex Filter Topology Set
namespace GuthMaynard.CitedZeros.Rich.PartX
open GuthMaynard.CitedZeros.Rich
/-! ## `ford_u_zero` -/
theorem ford_u_zero (N : ℕ) (t : ℝ) (hN : 1 ≤ N) (hNt : (N : ℝ) ≤ t) (R : ℕ) (hR : N < R)
    (hR2 : R ≤ 2 * N) :
    ‖∑ n ∈ Finset.Ioc N R, ((n : ℝ) : ℂ) ^ (-((t : ℂ) * I))‖ ≤
      9.463 * (N : ℝ) ^ (1 - 1 / (133.66 * (Real.log t / Real.log N) ^ 2)) := by
  set F : ℝ → ℂ := fun u => ∑ n ∈ Finset.Ioc N R, ((((n : ℝ) + u : ℝ)) : ℂ) ^ (-((t : ℂ) * I))
    with hF
  have hlim : Tendsto F (𝓝 0) (𝓝 (F 0)) := by
    apply tendsto_finsetSum
    intro n hn
    have hn1 : (1 : ℝ) ≤ n := by
      have := (Finset.mem_Ioc.mp hn).1
      exact_mod_cast (show 1 ≤ n by omega)
    have hslit : ((((n : ℝ) + 0 : ℝ)) : ℂ) ∈ slitPlane := by
      apply ofReal_mem_slitPlane.mpr; linarith
    have hc : ContinuousAt (fun u : ℝ => ((((n : ℝ) + u : ℝ)) : ℂ) ^ (-((t : ℂ) * I))) 0 :=
      ContinuousAt.comp (g := fun z : ℂ => z ^ (-((t : ℂ) * I))) (continuousAt_cpow_const hslit)
        (by fun_prop)
    exact hc.tendsto
  have hlim' : Tendsto (fun u => ‖F u‖) (𝓝[>] 0) (𝓝 ‖F 0‖) :=
    (hlim.mono_left nhdsWithin_le_nhds).norm
  have hev : ∀ᶠ u in 𝓝[>] (0 : ℝ), ‖F u‖ ≤
      9.463 * (N : ℝ) ^ (1 - 1 / (133.66 * (Real.log t / Real.log N) ^ 2)) := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with u hu
    have h := GuthMaynard.ford_exponential_sum_bound N t hN hNt u hu.1 hu.2.le (R : ℝ)
      (by exact_mod_cast hR) (by exact_mod_cast hR2)
    rw [Nat.floor_natCast] at h
    exact h
  have h0 := le_of_tendsto hlim' hev
  simpa [hF] using h0

end GuthMaynard.CitedZeros.Rich.PartX
end

section
open Complex Filter Topology Set
namespace GuthMaynard.CitedZeros.Rich

end GuthMaynard.CitedZeros.Rich
end

section
open Complex Filter Topology Set
namespace GuthMaynard.CitedZeros.Rich.PartX
open GuthMaynard.CitedZeros.Rich
/-! ## `abel_block` -/
lemma abel_gen (a : ℕ → ℂ) (b : ℕ → ℝ) (B : ℝ) (N : ℕ)
    (hbm : ∀ n, N < n → b (n + 1) ≤ b n) (k : ℕ)
    (hB : ∀ R' : ℕ, N < R' → R' ≤ N + k → ‖∑ n ∈ Finset.Ioc N R', a n‖ ≤ B) :
    ‖∑ n ∈ Finset.Ioc N (N + k), (b n : ℂ) * a n
      - (∑ n ∈ Finset.Ioc N (N + k), a n) * (b (N + k + 1) : ℂ)‖ ≤
      B * (b (N + 1) - b (N + k + 1)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have ih' := ih (fun R' h1 h2 => hB R' h1 (by omega))
    have hA := hB (N + k + 1) (by omega) (by omega)
    rw [show N + (k + 1) = N + k + 1 by ring, Finset.sum_Ioc_succ_top (by omega),
      Finset.sum_Ioc_succ_top (by omega)]
    rw [Finset.sum_Ioc_succ_top (by omega)] at hA
    set S := ∑ n ∈ Finset.Ioc N (N + k), (b n : ℂ) * a n
    set A := ∑ n ∈ Finset.Ioc N (N + k), a n
    have hd : 0 ≤ b (N + k + 1) - b (N + k + 1 + 1) := by
      linarith [hbm (N + k + 1) (by omega)]
    have : S + (b (N + k + 1) : ℂ) * a (N + k + 1) - (A + a (N + k + 1)) * (b (N + k + 1 + 1) : ℂ)
        = (S - A * b (N + k + 1)) +
          (A + a (N + k + 1)) * ((b (N + k + 1) - b (N + k + 1 + 1) : ℝ) : ℂ) := by
      push_cast; ring
    rw [this]
    have h2 : ‖(A + a (N + k + 1)) * ((b (N + k + 1) - b (N + k + 1 + 1) : ℝ) : ℂ)‖ ≤
        B * (b (N + k + 1) - b (N + k + 1 + 1)) := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hd]
      exact mul_le_mul_of_nonneg_right hA hd
    calc _ ≤ ‖S - A * b (N + k + 1)‖ +
          ‖(A + a (N + k + 1)) * ((b (N + k + 1) - b (N + k + 1 + 1) : ℝ) : ℂ)‖ :=
          norm_add_le _ _
      _ ≤ B * (b (N + 1) - b (N + k + 1)) + B * (b (N + k + 1) - b (N + k + 1 + 1)) :=
          add_le_add ih' h2
      _ = _ := by ring

theorem abel_block (σ t B : ℝ) (hσ : 0 ≤ σ) (hB0 : 0 ≤ B) (N R : ℕ) (hN : 1 ≤ N)
    (hB : ∀ R' : ℕ, N < R' → R' ≤ R →
      ‖∑ n ∈ Finset.Ioc N R', ((n : ℝ) : ℂ) ^ (-((t : ℂ) * I))‖ ≤ B) :
    ‖∑ n ∈ Finset.Ioc N R, ((n : ℝ) : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I))‖ ≤ (N : ℝ) ^ (-σ) * B := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  rcases le_or_gt R N with hRN | hRN
  · rw [Finset.Ioc_eq_empty (by omega)]
    simp only [Finset.sum_empty, norm_zero]
    positivity
  obtain ⟨k, rfl⟩ : ∃ k, R = N + k := ⟨R - N, by omega⟩
  set a : ℕ → ℂ := fun n => ((n : ℝ) : ℂ) ^ (-((t : ℂ) * I)) with ha
  set b : ℕ → ℝ := fun n => (n : ℝ) ^ (-σ) with hb
  have hterm : ∀ n ∈ Finset.Ioc N (N + k),
      ((n : ℝ) : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I)) = (b n : ℂ) * a n := by
    intro n hn
    have hn0 : (0 : ℝ) < n := by
      have := (Finset.mem_Ioc.mp hn).1
      exact_mod_cast (show 0 < n by omega)
    simp only [ha, hb]
    rw [neg_add, Complex.cpow_add _ _ (by exact_mod_cast hn0.ne'),
      Complex.ofReal_cpow hn0.le]
    push_cast; ring
  rw [Finset.sum_congr rfl hterm]
  have hbm : ∀ n, N < n → b (n + 1) ≤ b n := by
    intro n hn
    simp only [hb]
    have : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    exact Real.rpow_le_rpow_of_nonpos this (by push_cast; linarith) (by linarith)
  have h := abel_gen a b B N hbm k (fun R' h1 h2 => hB R' h1 h2)
  have hA := hB (N + k) hRN le_rfl
  have hbR : 0 ≤ b (N + k + 1) := Real.rpow_nonneg (by positivity) _
  have hbN : b (N + 1) ≤ (N : ℝ) ^ (-σ) :=
    Real.rpow_le_rpow_of_nonpos hNpos (by push_cast; linarith) (by linarith)
  set S := ∑ n ∈ Finset.Ioc N (N + k), (b n : ℂ) * a n
  set A := ∑ n ∈ Finset.Ioc N (N + k), a n
  have h3 : ‖A * (b (N + k + 1) : ℂ)‖ ≤ B * b (N + k + 1) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hbR]
    exact mul_le_mul_of_nonneg_right hA hbR
  calc ‖S‖ = ‖(S - A * (b (N + k + 1) : ℂ)) + A * (b (N + k + 1) : ℂ)‖ := by ring_nf
    _ ≤ ‖S - A * (b (N + k + 1) : ℂ)‖ + ‖A * (b (N + k + 1) : ℂ)‖ := norm_add_le _ _
    _ ≤ B * (b (N + 1) - b (N + k + 1)) + B * b (N + k + 1) := add_le_add h h3
    _ = b (N + 1) * B := by ring
    _ ≤ (N : ℝ) ^ (-σ) * B := mul_le_mul_of_nonneg_right hbN hB0

end GuthMaynard.CitedZeros.Rich.PartX
end

section
open Complex Filter Topology Set
namespace GuthMaynard.CitedZeros.Rich

end GuthMaynard.CitedZeros.Rich
end

section
open Complex Filter Topology Set
namespace GuthMaynard.CitedZeros.Rich.PartX
open GuthMaynard.CitedZeros.Rich
/-! ## `dyadic_sum` -/
lemma block_bound (t σ : ℝ) (ht : 2 ≤ t) (hσ0 : 1 / 2 ≤ σ) (j T : ℕ) (hT : (T : ℝ) ≤ t)
    (hj : 2 ^ j < T) :
    ‖∑ n ∈ Finset.Ioc (2 ^ j) (min (2 ^ (j + 1)) T),
        ((n : ℝ) : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I))‖ ≤
      9.463 * Real.exp (gexp σ (Real.log t) j) := by
  have hN : 1 ≤ 2 ^ j := Nat.one_le_two_pow
  have hNt : ((2 ^ j : ℕ) : ℝ) ≤ t := by
    have : ((2 ^ j : ℕ) : ℝ) < T := by exact_mod_cast hj
    linarith
  have h := PartX.abel_block σ t
    (9.463 * ((2 ^ j : ℕ) : ℝ) ^ (1 - 1 / (133.66 * (Real.log t / Real.log (2 ^ j : ℕ)) ^ 2)))
    (by linarith) (by positivity) (2 ^ j) (min (2 ^ (j + 1)) T) hN
    (fun R' h1 h2 => PartX.ford_u_zero (2 ^ j) t hN hNt R' h1
      (by have := min_le_left (2 ^ (j + 1)) T; rw [pow_succ] at this; omega))
  refine h.trans (le_of_eq ?_)
  have hL : 0 < Real.log t := Real.log_pos (by linarith)
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hNpos : (0 : ℝ) < ((2 ^ j : ℕ) : ℝ) := by positivity
  rw [← mul_assoc, mul_comm _ (9.463 : ℝ), mul_assoc, ← Real.rpow_add hNpos]
  congr 1
  rw [Real.rpow_def_of_pos hNpos]
  congr 1
  push_cast
  rw [Real.log_pow]
  unfold gexp
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · simp
  · have hx : (0 : ℝ) < j * Real.log 2 := by positivity
    field_simp
    ring

set_option linter.unusedVariables false in
theorem dyadic_sum (t σ : ℝ) (ht : 2 ≤ t) (hσ0 : 1 / 2 ≤ σ) (hσ1 : σ ≤ 1) :
    ‖∑ n ∈ Finset.Icc 1 ⌊t⌋₊, ((n : ℝ) : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I))‖ ≤
      1 + 9.463 * ∑ j ∈ Finset.range (⌊Real.log t / Real.log 2⌋₊ + 1),
        Real.exp (gexp σ (Real.log t) j) := by
  set T := ⌊t⌋₊ with hTdef
  set J := ⌊Real.log t / Real.log 2⌋₊ with hJdef
  set f : ℕ → ℂ := fun n => ((n : ℝ) : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I)) with hf
  have hT1 : 1 ≤ T := Nat.le_floor (by push_cast; linarith)
  have hTt : (T : ℝ) ≤ t := Nat.floor_le (by linarith)
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hTJ : T ≤ 2 ^ (J + 1) := by
    have h1 : Real.log t / Real.log 2 < J + 1 := Nat.lt_floor_add_one _
    have h2 : Real.log t < Real.log ((2 : ℝ) ^ (J + 1)) := by
      rw [Real.log_pow]; push_cast; rwa [div_lt_iff₀ hl2] at h1
    have h3 : t < (2 : ℝ) ^ (J + 1) := by
      rwa [Real.log_lt_log_iff (by linarith) (by positivity)] at h2
    have : (T : ℝ) < ((2 ^ (J + 1) : ℕ) : ℝ) := by push_cast; linarith
    exact_mod_cast this.le
  set m : ℕ → ℕ := fun j => min (2 ^ j) T with hm
  have hmono1 : ∀ j, m j ≤ m (j + 1) := fun j =>
    min_le_min_right _ (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hmono : Monotone m := monotone_nat_of_le_succ hmono1
  have htel : ∀ K, ∑ n ∈ Finset.Ioc (m 0) (m K), f n =
      ∑ j ∈ Finset.range K, ∑ n ∈ Finset.Ioc (m j) (m (j + 1)), f n := by
    intro K
    induction K with
    | zero => simp
    | succ K ih =>
      rw [Finset.sum_range_succ, ← ih,
        Finset.sum_Ioc_consecutive _ (hmono (Nat.zero_le K)) (hmono1 K)]
  have hm0 : m 0 = 1 := by simp [hm]; omega
  have hmJ : m (J + 1) = T := by simp [hm]; omega
  have hsplit : ∑ n ∈ Finset.Icc 1 T, f n = f 1 + ∑ n ∈ Finset.Ioc (m 0) (m (J + 1)), f n := by
    rw [hm0, hmJ, show Finset.Icc 1 T = Finset.Ioc 0 T by ext x; simp; omega,
      ← Finset.sum_Ioc_consecutive _ (Nat.zero_le 1) hT1]
    simp
  have hblock : ∀ j ∈ Finset.range (J + 1), ‖∑ n ∈ Finset.Ioc (m j) (m (j + 1)), f n‖ ≤
      9.463 * Real.exp (gexp σ (Real.log t) j) := by
    intro j _
    by_cases hj : 2 ^ j < T
    · have e1 : m j = 2 ^ j := min_eq_left hj.le
      rw [e1]
      exact block_bound t σ ht hσ0 j T hTt hj
    · have e1 : m j = T := min_eq_right (not_lt.mp hj)
      have e2 : m (j + 1) = T :=
        min_eq_right ((not_lt.mp hj).trans (Nat.pow_le_pow_right (by norm_num) (by omega)))
      rw [e1, e2, Finset.Ioc_self]
      simp only [Finset.sum_empty, norm_zero]
      positivity
  have hf1 : ‖f 1‖ = 1 := by simp [hf]
  rw [hsplit, htel, Finset.mul_sum]
  calc _ ≤ ‖f 1‖ + ‖∑ j ∈ Finset.range (J + 1), ∑ n ∈ Finset.Ioc (m j) (m (j + 1)), f n‖ :=
        norm_add_le _ _
    _ ≤ 1 + ∑ j ∈ Finset.range (J + 1), 9.463 * Real.exp (gexp σ (Real.log t) j) := by
      rw [hf1]
      exact add_le_add le_rfl ((norm_sum_le _ _).trans (Finset.sum_le_sum hblock))

end GuthMaynard.CitedZeros.Rich.PartX
end

section
open Complex Filter Topology Set
namespace GuthMaynard.CitedZeros.Rich
alias dyadic_sum := GuthMaynard.CitedZeros.Rich.PartX.dyadic_sum

end GuthMaynard.CitedZeros.Rich
end

section
open Complex Filter Topology Set
namespace GuthMaynard.CitedZeros.Rich.PartX
open GuthMaynard.CitedZeros.Rich
/-! ## `exp_sum_bound` -/
lemma young_step (s x L : ℝ) (hs : 0 ≤ s) (hx : 0 ≤ x) (hL : 0 < L) :
    s * x - x ^ 3 / (133.66 * L ^ 2) ≤
      17 * s ^ (3 / 2 : ℝ) * L - x ^ 3 / (2 * 133.66 * L ^ 2) := by
  set r := Real.sqrt s with hr
  have hr0 : 0 ≤ r := Real.sqrt_nonneg s
  have hsr : s = r ^ 2 := (Real.sq_sqrt hs).symm
  have h32 : s ^ (3 / 2 : ℝ) = r ^ 3 := by
    rw [hr, Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hs]; norm_num
  rw [h32]
  have hL2 : 0 < L ^ 2 := by positivity
  suffices h : s * x ≤ 17 * r ^ 3 * L + x ^ 3 / (2 * 133.66 * L ^ 2) by
    have : x ^ 3 / (133.66 * L ^ 2) = 2 * (x ^ 3 / (2 * 133.66 * L ^ 2)) := by
      field_simp
    linarith
  rcases le_or_gt x (17 * r * L) with h | h
  · have h1 : s * x ≤ r ^ 2 * (17 * r * L) := by
      rw [hsr]; exact mul_le_mul_of_nonneg_left h (by positivity)
    have h2 : 0 ≤ x ^ 3 / (2 * 133.66 * L ^ 2) := by positivity
    have h3 : r ^ 2 * (17 * r * L) = 17 * r ^ 3 * L := by ring
    linarith
  · have hx2 : (17 * r * L) ^ 2 ≤ x ^ 2 := pow_le_pow_left₀ (by positivity) h.le 2
    have h1 : s * x ≤ x ^ 3 / (2 * 133.66 * L ^ 2) := by
      rw [le_div_iff₀ (by positivity), hsr]
      have := mul_le_mul_of_nonneg_left hx2 hx
      have h0 : 0 ≤ x * r ^ 2 * L ^ 2 := by positivity
      nlinarith
    have : 0 ≤ 17 * r ^ 3 * L := by positivity
    linarith

lemma tail_sum (a c : ℝ) (ha : 1 ≤ a) (hc : 0 < c) (J : ℕ) :
    ∑ j ∈ Finset.range J, Real.exp (-(c * ((j : ℝ) / a) ^ 3)) ≤ (3 + 1 / c) * a := by
  have ha0 : 0 < a := by linarith
  set y := c / a with hy
  have hy0 : 0 < y := div_pos hc ha0
  set r := Real.exp (-y) with hrdef
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : r < 1 := by
    have := Real.exp_lt_exp.mpr (show -y < 0 by linarith)
    rwa [Real.exp_zero] at this
  have hterm : ∀ j ∈ Finset.range J, Real.exp (-(c * ((j : ℝ) / a) ^ 3)) ≤
      (if (j : ℝ) < a then 1 else 0) + r ^ j := by
    intro j _
    split_ifs with hja
    · have h1 : Real.exp (-(c * ((j : ℝ) / a) ^ 3)) ≤ 1 :=
        Real.exp_le_one_iff.mpr (by
          have : 0 ≤ c * ((j : ℝ) / a) ^ 3 := by positivity
          linarith)
      have : 0 ≤ r ^ j := pow_nonneg hr0 j
      linarith
    · push Not at hja
      have hq : 1 ≤ (j : ℝ) / a := by rw [le_div_iff₀ ha0]; linarith
      have hq3 : (j : ℝ) / a ≤ ((j : ℝ) / a) ^ 3 := by
        have := mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ (j : ℝ) / a)
          (by linarith : (0 : ℝ) ≤ (j : ℝ) / a - 1)) (by linarith : (0 : ℝ) ≤ (j : ℝ) / a + 1)
        nlinarith
      rw [zero_add, hrdef, ← Real.exp_nat_mul]
      apply Real.exp_le_exp.mpr
      have : (j : ℝ) * -y = -(c * ((j : ℝ) / a)) := by rw [hy]; ring
      rw [this]
      nlinarith
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_add_distrib]
  have h1 : ∑ j ∈ Finset.range J, (if (j : ℝ) < a then (1 : ℝ) else 0) ≤ a + 1 := by
    rw [Finset.sum_boole]
    have hsub : Finset.filter (fun j : ℕ => (j : ℝ) < a) (Finset.range J) ⊆
        Finset.range (⌊a⌋₊ + 1) := by
      intro j hj
      simp only [Finset.mem_filter] at hj
      simp only [Finset.mem_range]
      have := Nat.le_floor hj.2.le
      omega
    calc _ ≤ ((Finset.range (⌊a⌋₊ + 1)).card : ℝ) := by
          exact_mod_cast Finset.card_le_card hsub
      _ = ⌊a⌋₊ + 1 := by simp
      _ ≤ a + 1 := by linarith [Nat.floor_le ha0.le]
  have h2 : ∑ j ∈ Finset.range J, r ^ j ≤ 1 + a / c := by
    have := geom_sum_Ico_le_of_lt_one (m := 0) (n := J) hr0 hr1
    rw [← Finset.range_eq_Ico, pow_zero] at this
    refine this.trans ?_
    have hexp : (1 + y) * r ≤ 1 := by
      rw [hrdef]
      have := Real.add_one_le_exp y
      have h' : Real.exp y * Real.exp (-y) = 1 := by rw [← Real.exp_add]; simp
      nlinarith [Real.exp_pos (-y)]
    rw [div_le_iff₀ (by linarith)]
    have e1 : a / c = 1 / y := by rw [hy]; field_simp
    have e2 : (1 + 1 / y) * (1 - r) = ((1 + y) - (1 + y) * r) / y := by field_simp; ring
    rw [e1, e2, le_div_iff₀ hy0]
    linarith
  have : (3 + 1 / c) * a = 3 * a + a / c := by ring
  linarith

theorem exp_sum_bound : ∃ B C : ℝ, 0 ≤ B ∧ 0 ≤ C ∧ ∀ L : ℝ, 1 ≤ L → ∀ σ : ℝ, 1 / 2 ≤ σ → σ ≤ 1 →
    ∀ J : ℕ, ∑ j ∈ Finset.range J, Real.exp (gexp σ L j) ≤
      C * Real.exp (B * (1 - σ) ^ (3 / 2 : ℝ) * L) * L ^ (2 / 3 : ℝ) := by
  set c₀ : ℝ := (Real.log 2) ^ 3 / (2 * 133.66) with hc₀
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hc0 : 0 < c₀ := by positivity
  refine ⟨17, 3 + 1 / c₀, by norm_num, by positivity, fun L hL σ hσ0 hσ1 J => ?_⟩
  have hL0 : 0 < L := by linarith
  set a : ℝ := L ^ (2 / 3 : ℝ) with ha
  have ha1 : 1 ≤ a := Real.one_le_rpow hL (by norm_num)
  have ha3 : a ^ 3 = L ^ 2 := by
    rw [ha, ← Real.rpow_natCast, ← Real.rpow_mul hL0.le]; norm_num
  set E := Real.exp (17 * (1 - σ) ^ (3 / 2 : ℝ) * L) with hE
  have hterm : ∀ j ∈ Finset.range J,
      Real.exp (gexp σ L j) ≤ E * Real.exp (-(c₀ * ((j : ℝ) / a) ^ 3)) := by
    intro j _
    rw [hE, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have h := young_step (1 - σ) (j * Real.log 2) L (by linarith) (by positivity) hL0
    have he : c₀ * ((j : ℝ) / a) ^ 3 = (j * Real.log 2) ^ 3 / (2 * 133.66 * L ^ 2) := by
      rw [div_pow, ha3, hc₀]; field_simp
    unfold gexp
    rw [he]; linarith
  calc _ ≤ ∑ j ∈ Finset.range J, E * Real.exp (-(c₀ * ((j : ℝ) / a) ^ 3)) :=
        Finset.sum_le_sum hterm
    _ = E * ∑ j ∈ Finset.range J, Real.exp (-(c₀ * ((j : ℝ) / a) ^ 3)) := by rw [Finset.mul_sum]
    _ ≤ E * ((3 + 1 / c₀) * a) :=
        mul_le_mul_of_nonneg_left (tail_sum a c₀ ha1 hc0 J) (Real.exp_pos _).le
    _ = _ := by ring

end GuthMaynard.CitedZeros.Rich.PartX
end

section
open Complex Filter Topology Set
namespace GuthMaynard.CitedZeros.Rich
alias exp_sum_bound := GuthMaynard.CitedZeros.Rich.PartX.exp_sum_bound

end GuthMaynard.CitedZeros.Rich
end

section
open Complex Filter Topology Set
namespace GuthMaynard.CitedZeros.Rich.PartY
open GuthMaynard.CitedZeros.Rich
/-- Abel summation step: `∑_{M<n≤R} a n z n - a R S R` is bounded by `(a(M+1) - a R) B`. -/
theorem abel_aux (a : ℕ → ℝ) (z : ℕ → ℂ) (B : ℝ) (M Rm : ℕ)
    (ha : ∀ n, M < n → a (n + 1) ≤ a n)
    (hB : ∀ R', M < R' → R' ≤ Rm → ‖∑ n ∈ Finset.Ioc M R', z n‖ ≤ B) :
    ∀ R, M + 1 ≤ R → R ≤ Rm → ‖∑ n ∈ Finset.Ioc M R, (a n : ℂ) * z n -
        (a R : ℂ) * ∑ n ∈ Finset.Ioc M R, z n‖ ≤ (a (M + 1) - a R) * B := by
  intro R hR
  induction R, hR using Nat.le_induction with
  | base =>
    intro _
    simp [Nat.Ioc_succ_singleton]
  | succ R hR ih =>
    intro hRm
    have ih := ih (by omega)
    have hMR : M < R := by omega
    rw [Finset.sum_Ioc_succ_top (by omega), Finset.sum_Ioc_succ_top (by omega)]
    have heq : (∑ n ∈ Finset.Ioc M R, (a n : ℂ) * z n + (a (R + 1) : ℂ) * z (R + 1)) -
        (a (R + 1) : ℂ) * (∑ n ∈ Finset.Ioc M R, z n + z (R + 1)) =
        (∑ n ∈ Finset.Ioc M R, (a n : ℂ) * z n - (a R : ℂ) * ∑ n ∈ Finset.Ioc M R, z n) +
          ((a R - a (R + 1) : ℝ) : ℂ) * ∑ n ∈ Finset.Ioc M R, z n := by
      push_cast; ring
    rw [heq]
    have h1 := hB R hMR (by omega)
    have h2 : 0 ≤ a R - a (R + 1) := by linarith [ha R hMR]
    calc _ ≤ ‖∑ n ∈ Finset.Ioc M R, (a n : ℂ) * z n - (a R : ℂ) * ∑ n ∈ Finset.Ioc M R, z n‖ +
          ‖((a R - a (R + 1) : ℝ) : ℂ) * ∑ n ∈ Finset.Ioc M R, z n‖ := norm_add_le _ _
      _ ≤ (a (M + 1) - a R) * B + (a R - a (R + 1)) * B := by
          gcongr
          rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg h2]
          gcongr
      _ = _ := by ring

/-- Abel's inequality. -/
theorem abel_ineq (a : ℕ → ℝ) (z : ℕ → ℂ) (B : ℝ) (M R : ℕ) (hR : M + 1 ≤ R)
    (ha : ∀ n, M < n → a (n + 1) ≤ a n) (ha0 : 0 ≤ a R)
    (hB : ∀ R', M < R' → R' ≤ R → ‖∑ n ∈ Finset.Ioc M R', z n‖ ≤ B) :
    ‖∑ n ∈ Finset.Ioc M R, (a n : ℂ) * z n‖ ≤ a (M + 1) * B := by
  have h1 := abel_aux a z B M R ha hB R hR le_rfl
  have h2 := hB R (by omega) le_rfl
  calc _ ≤ ‖∑ n ∈ Finset.Ioc M R, (a n : ℂ) * z n -
        (a R : ℂ) * ∑ n ∈ Finset.Ioc M R, z n‖ + ‖(a R : ℂ) * ∑ n ∈ Finset.Ioc M R, z n‖ :=
        norm_le_norm_sub_add _ _
    _ ≤ (a (M + 1) - a R) * B + a R * B := by
        gcongr
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ha0]
        gcongr
    _ = _ := by ring

theorem log_succ_sub_le (n : ℕ) (hn : 1 ≤ n) :
    Real.log ((n : ℝ) + 1) - Real.log n ≤ 1 / n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [← Real.log_div (by positivity) hn'.ne']
  have := Real.log_le_sub_one_of_pos (x := ((n : ℝ) + 1) / n) (by positivity)
  have e : ((n : ℝ) + 1) / n - 1 = 1 / n := by field_simp; ring
  linarith

theorem le_log_succ_sub (n : ℕ) (hn : 1 ≤ n) :
    1 / ((n : ℝ) + 1) ≤ Real.log ((n : ℝ) + 1) - Real.log n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h := Real.log_le_sub_one_of_pos (x := (n : ℝ) / (n + 1)) (by positivity)
  rw [Real.log_div hn'.ne' (by positivity)] at h
  have e : (n : ℝ) / (n + 1) - 1 = -(1 / (n + 1)) := by field_simp; ring
  linarith

theorem log_diff_anti (n : ℕ) (hn : 1 ≤ n) :
    Real.log ((n : ℝ) + 2) - Real.log ((n : ℝ) + 1) ≤ Real.log ((n : ℝ) + 1) - Real.log n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [← Real.log_div (by positivity) (by positivity), ← Real.log_div (by positivity) hn'.ne']
  apply Real.log_le_log (by positivity)
  rw [div_le_div_iff₀ (by positivity) hn']
  nlinarith

/-- `n^{-it} = exp(2πi f(n))` with `f(n) = -t log n / (2π)`. -/
theorem cpow_neg_tI_eq (t : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    ((n : ℝ) : ℂ) ^ (-((t : ℂ) * I)) =
      Complex.exp (((2 * Real.pi * (-t * Real.log n / (2 * Real.pi)) : ℝ) : ℂ) * I) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hn'.ne'), ← Complex.ofReal_log hn'.le]
  congr 1
  have : (2 * Real.pi * (-t * Real.log n / (2 * Real.pi))) = -t * Real.log n := by
    field_simp
  rw [this]; push_cast; ring

/-- `n^{-(σ+it)} = n^{-σ} n^{-it}`. -/
theorem cpow_split (σ t : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    ((n : ℝ) : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I)) =
      (((n : ℝ) ^ (-σ) : ℝ) : ℂ) * ((n : ℝ) : ℂ) ^ (-((t : ℂ) * I)) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [Complex.ofReal_cpow hn'.le, neg_add, Complex.cpow_add _ _ (by exact_mod_cast hn'.ne')]
  push_cast; ring_nf

/-- Kusmin–Landau on a block: `‖∑_{M<n≤R} n^{-it}‖ ≤ 2π(2M+2)/t`. -/
theorem exp_block (t : ℝ) (ht : 0 < t) (M R : ℕ) (hM1 : 1 ≤ M) (htM : t ≤ M + 1)
    (hR : R ≤ 2 * M) :
    ‖∑ n ∈ Finset.Ioc M R, ((n : ℝ) : ℂ) ^ (-((t : ℂ) * I))‖ ≤
      2 * Real.pi * (2 * M + 2) / t := by
  have hpi := Real.pi_gt_three
  set f : ℕ → ℝ := fun n => -t * Real.log n / (2 * Real.pi) with hf
  set δ : ℝ := (t / (2 * M + 2)) / (2 * Real.pi) with hδ
  have hMpos : (0 : ℝ) < 2 * M + 2 := by positivity
  have hdiff : ∀ n : ℕ, f (n + 1) - f n =
      -(t * (Real.log ((n : ℝ) + 1) - Real.log n)) / (2 * Real.pi) := by
    intro n; simp only [hf]; push_cast; ring
  have hsum : ∑ n ∈ Finset.Ioc M R, ((n : ℝ) : ℂ) ^ (-((t : ℂ) * I)) =
      ∑ n ∈ Finset.Ioc M R, Complex.exp (((2 * Real.pi * f n : ℝ) : ℂ) * I) := by
    apply Finset.sum_congr rfl
    intro n hn
    rw [Finset.mem_Ioc] at hn
    exact cpow_neg_tI_eq t n (by omega)
  rw [hsum]
  have hδ0 : 0 < δ := by positivity
  have htM2 : t / (2 * M + 2) ≤ 1 / 2 := by
    rw [div_le_iff₀ hMpos]; linarith
  have hδ1 : δ ≤ 1 / 2 := by
    rw [hδ, div_le_iff₀ (by positivity)]; nlinarith
  have key := ExponentialSums.kusmin_landau (f := f) (a := M) (b := R) (m := -1) hδ0 hδ1
    (fun n hn1 hn2 => by
      rw [hdiff]
      have hn : 1 ≤ n := by omega
      have hD := log_succ_sub_le n hn
      have hD0 := le_log_succ_sub n hn
      have hnr : (1 : ℝ) ≤ n := by exact_mod_cast hn
      have htn : t ≤ n := by
        have : (M : ℝ) + 1 ≤ n := by exact_mod_cast hn1
        linarith
      set D := Real.log ((n : ℝ) + 1) - Real.log n
      have htD : t * D ≤ 1 := by
        calc t * D ≤ t * (1 / n) := by gcongr
          _ ≤ 1 := by rw [mul_one_div, div_le_one (by linarith)]; exact htn
      rw [hδ]
      have h2pi : (0 : ℝ) < 2 * Real.pi := by positivity
      rw [show ((-1 : ℤ) : ℝ) + t / (2 * M + 2) / (2 * Real.pi) =
        (t / (2 * M + 2) - 2 * Real.pi) / (2 * Real.pi) by push_cast; field_simp; ring]
      rw [div_le_div_iff_of_pos_right h2pi]
      linarith)
    (fun n hn1 hn2 => by
      rw [hdiff]
      have hn : 1 ≤ n := by omega
      have hD0 := le_log_succ_sub n hn
      set D := Real.log ((n : ℝ) + 1) - Real.log n
      have h2pi : (0 : ℝ) < 2 * Real.pi := by positivity
      rw [hδ, show ((-1 : ℤ) : ℝ) + 1 - t / (2 * M + 2) / (2 * Real.pi) =
        -(t / (2 * M + 2)) / (2 * Real.pi) by push_cast; ring]
      rw [div_le_div_iff_of_pos_right h2pi, neg_le_neg_iff]
      have hnM : (n : ℝ) + 1 ≤ 2 * M + 2 := by
        have : (n : ℝ) ≤ 2 * M := by exact_mod_cast hn2.trans hR
        linarith
      calc t / (2 * M + 2) = t * (1 / (2 * M + 2)) := by ring
        _ ≤ t * (1 / ((n : ℝ) + 1)) := by gcongr
        _ ≤ t * D := by gcongr)
    (fun n hn1 hn2 => by
      have hn : 1 ≤ n := by omega
      have e := hdiff (n + 1)
      rw [hdiff, show n + 2 = n + 1 + 1 by ring, e]
      have h2pi : (0 : ℝ) < 2 * Real.pi := by positivity
      rw [div_le_div_iff_of_pos_right h2pi, neg_le_neg_iff]
      have := log_diff_anti n hn
      push_cast
      rw [show (n : ℝ) + 1 + 1 = n + 2 by ring]
      gcongr)
  refine key.trans (le_of_eq ?_)
  rw [hδ]; field_simp

/-- A dyadic block of the Dirichlet polynomial: `‖∑_{M<n≤R} n^{-s}‖ ≤ 4π√(M+1)/t`. -/
theorem block_bound (t σ : ℝ) (hσ : 1 / 2 ≤ σ) (ht : 0 < t) (M R : ℕ) (hM1 : 1 ≤ M)
    (htM : t ≤ M + 1) (hR : R ≤ 2 * M) :
    ‖∑ n ∈ Finset.Ioc M R, ((n : ℝ) : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I))‖ ≤
      4 * Real.pi * Real.sqrt ((M : ℝ) + 1) / t := by
  by_cases hRM : M + 1 ≤ R
  swap
  · rw [Finset.Ioc_eq_empty (by omega)]; simp; positivity
  have hsum : ∑ n ∈ Finset.Ioc M R, ((n : ℝ) : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I)) =
      ∑ n ∈ Finset.Ioc M R, (((n : ℝ) ^ (-σ) : ℝ) : ℂ) * ((n : ℝ) : ℂ) ^ (-((t : ℂ) * I)) := by
    apply Finset.sum_congr rfl
    intro n hn
    rw [Finset.mem_Ioc] at hn
    exact cpow_split σ t n (by omega)
  rw [hsum]
  have hσ0 : 0 < σ := by linarith
  have h := abel_ineq (fun n : ℕ => (n : ℝ) ^ (-σ))
    (fun n : ℕ => ((n : ℝ) : ℂ) ^ (-((t : ℂ) * I))) (2 * Real.pi * (2 * M + 2) / t) M R hRM
    (fun n hn => by
      have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
      show ((n + 1 : ℕ) : ℝ) ^ (-σ) ≤ (n : ℝ) ^ (-σ)
      rw [Real.rpow_neg (by positivity), Real.rpow_neg hn'.le]
      apply inv_anti₀ (Real.rpow_pos_of_pos hn' _)
      apply Real.rpow_le_rpow hn'.le (by push_cast; linarith) hσ0.le)
    (by positivity)
    (fun R' h1 h2 => exp_block t ht M R' hM1 htM (h2.trans hR))
  refine h.trans ?_
  set x : ℝ := (M : ℝ) + 1 with hx
  have hx1 : 1 ≤ x := by rw [hx]; linarith [(Nat.cast_nonneg M : (0 : ℝ) ≤ M)]
  have hcast : (((M + 1 : ℕ) : ℝ)) = x := by push_cast; rfl
  rw [hcast]
  have hle : x ^ (-σ) ≤ x ^ (-(1 / 2 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  have hsq : x ^ (-(1 / 2 : ℝ)) = 1 / Real.sqrt x := by
    rw [Real.rpow_neg (by linarith), Real.sqrt_eq_rpow, one_div]; norm_num
  have e : 2 * Real.pi * (2 * (M : ℝ) + 2) / t = 4 * Real.pi * x / t := by rw [hx]; ring
  rw [e]
  calc x ^ (-σ) * (4 * Real.pi * x / t) ≤ x ^ (-(1 / 2 : ℝ)) * (4 * Real.pi * x / t) := by
        gcongr
    _ = 4 * Real.pi * (x / Real.sqrt x) / t := by rw [hsq]; ring
    _ = _ := by rw [Real.div_sqrt]

/-- The middle range `T < n ≤ T 2^K`, summed over dyadic blocks. -/
theorem middle_bound (t σ : ℝ) (hσ : 1 / 2 ≤ σ) (ht : 0 < t) (T : ℕ) (hT1 : 1 ≤ T)
    (htT : t ≤ T + 1) (K : ℕ) :
    ‖∑ n ∈ Finset.Ioc T (T * 2 ^ K), ((n : ℝ) : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I))‖ ≤
      16 * Real.pi * Real.sqrt ((T * 2 ^ K : ℕ) : ℝ) / t := by
  induction K with
  | zero => simp; positivity
  | succ K ih =>
    have hM1 : 1 ≤ T * 2 ^ K := Nat.one_le_iff_ne_zero.mpr (by positivity)
    have hTM : T ≤ T * 2 ^ K := Nat.le_mul_of_pos_right T (by positivity)
    have h2 : T * 2 ^ (K + 1) = 2 * (T * 2 ^ K) := by ring
    rw [← Finset.sum_Ioc_consecutive _ hTM (by rw [h2]; omega)]
    have hblk := block_bound t σ hσ ht (T * 2 ^ K) (T * 2 ^ (K + 1)) hM1
      (by have : (T : ℝ) ≤ (T * 2 ^ K : ℕ) := by exact_mod_cast hTM
          linarith) (by rw [h2])
    set M := T * 2 ^ K with hMdef
    have hMr : (1 : ℝ) ≤ M := by exact_mod_cast hM1
    have hc : ((T * 2 ^ (K + 1) : ℕ) : ℝ) = 2 * (M : ℝ) := by rw [h2]; push_cast; ring
    rw [hc]
    have hs2 : Real.sqrt (2 * (M : ℝ)) = Real.sqrt 2 * Real.sqrt M :=
      Real.sqrt_mul (by norm_num) _
    have hM1' : Real.sqrt ((M : ℝ) + 1) ≤ Real.sqrt (2 * (M : ℝ)) :=
      Real.sqrt_le_sqrt (by linarith)
    have hsqrt2 : (4 : ℝ) / 3 ≤ Real.sqrt 2 := by
      rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
    have hu : 0 ≤ Real.sqrt (M : ℝ) := Real.sqrt_nonneg _
    have hpi := Real.pi_pos
    calc _ ≤ ‖∑ n ∈ Finset.Ioc T M, ((n : ℝ) : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I))‖ +
          ‖∑ n ∈ Finset.Ioc M (T * 2 ^ (K + 1)), ((n : ℝ) : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I))‖ :=
          norm_add_le _ _
      _ ≤ 16 * Real.pi * Real.sqrt (M : ℝ) / t + 4 * Real.pi * Real.sqrt (2 * (M : ℝ)) / t := by
          gcongr
          exact hblk.trans (by gcongr)
      _ ≤ _ := by
          rw [← add_div]
          gcongr
          rw [hs2]
          nlinarith [mul_nonneg hpi.le hu]

/-- The Euler–Maclaurin remainder integral. -/
theorem integral_bound (s : ℂ) (hs : 0 < s.re) (N : ℕ) (hN : 0 < N) :
    ‖∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ (s + 1)‖ ≤
      (N : ℝ) ^ (-s.re) / (2 * s.re) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hlt : -(s.re + 1) < -1 := by linarith
  have hint := integrableOn_Ioi_rpow_of_lt hlt hN'
  refine (MeasureTheory.norm_integral_le_of_norm_le (g := fun x => (1 / 2 : ℝ) * x ^ (-(s.re + 1)))
    (hint.const_mul _) ?_).trans (le_of_eq ?_)
  · refine (MeasureTheory.ae_restrict_iff' measurableSet_Ioi).mpr
      (Filter.Eventually.of_forall fun x hx => ?_)
    have hx0 : (0 : ℝ) < x := hN'.trans hx
    have e : ((⌊x⌋ : ℂ) + 1 / 2 - x) = (((⌊x⌋ : ℝ) + 1 / 2 - x : ℝ) : ℂ) := by push_cast; ring
    rw [e, norm_div, Complex.norm_real, Complex.norm_cpow_eq_rpow_re_of_pos hx0]
    have h1 := Int.floor_le x
    have h2 := Int.lt_floor_add_one x
    have hab : ‖((⌊x⌋ : ℝ) + 1 / 2 - x)‖ ≤ 1 / 2 := by
      rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith
    have hre : (s + 1).re = s.re + 1 := by simp
    rw [hre, Real.rpow_neg hx0.le, div_eq_mul_inv]
    gcongr
  · rw [MeasureTheory.integral_const_mul, integral_Ioi_rpow_of_lt hlt hN']
    have : -(s.re + 1) + 1 = -s.re := by ring
    rw [this]
    field_simp

/-- Reindexing the `riemannZeta0` sum. -/
theorem range_sum_eq (s : ℂ) (hs : s ≠ 0) (N T : ℕ) (hTN : T ≤ N) :
    ∑ n ∈ Finset.range (N + 1), 1 / (n : ℂ) ^ s =
      ∑ n ∈ Finset.Icc 1 T, ((n : ℝ) : ℂ) ^ (-s) + ∑ n ∈ Finset.Ioc T N, ((n : ℝ) : ℂ) ^ (-s) := by
  rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega)]
  have h0 : 1 / ((0 : ℕ) : ℂ) ^ s = 0 := by simp [Complex.zero_cpow hs]
  rw [h0, zero_add]
  have hI : Finset.Icc 1 T = Finset.Ioc 0 T := by ext n; simp; omega
  have hI2 : Finset.Ico (0 + 1) (N + 1) = Finset.Ioc 0 N := by ext n; simp; omega
  rw [hI, hI2, Finset.sum_Ioc_consecutive _ (Nat.zero_le T) hTN]
  apply Finset.sum_congr rfl
  intro n _
  rw [Complex.cpow_neg, Complex.ofReal_natCast, one_div]

theorem approx_formula : ∃ K t₀ : ℝ, 0 ≤ K ∧ ∀ t : ℝ, t₀ ≤ t → ∀ σ : ℝ, 1 / 2 ≤ σ → σ ≤ 1 →
    ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I) -
      ∑ n ∈ Finset.Icc 1 ⌊t⌋₊, ((n : ℝ) : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I))‖ ≤ K := by
  refine ⟨16 * Real.pi + 10, 4, by positivity, fun t ht σ hσ0 hσ1 => ?_⟩
  have hpi := Real.pi_pos
  have htpos : 0 < t := by linarith
  set s : ℂ := (σ : ℂ) + (t : ℂ) * I with hsdef
  have hsre : s.re = σ := by simp [hsdef]
  have hsim : s.im = t := by simp [hsdef]
  have hs0 : s ≠ 0 := by intro h; rw [h] at hsim; simp at hsim; linarith
  have hs1 : s ≠ 1 := by intro h; rw [h] at hsim; simp at hsim; linarith
  set T := ⌊t⌋₊ with hTdef
  have hT1 : 1 ≤ T := Nat.le_floor (by push_cast; linarith)
  have hTt : (T : ℝ) ≤ t := Nat.floor_le htpos.le
  have htT : t ≤ T + 1 := (Nat.lt_floor_add_one t).le
  set L := Nat.log 2 T with hL
  set N := T * 2 ^ L with hNdef
  have hpow : 2 ^ L ≤ T := Nat.pow_log_le_self 2 (by omega)
  have hpow2 : T < 2 ^ (L + 1) := Nat.lt_pow_succ_log_self (by norm_num) T
  have hNT : N ≤ T * T := Nat.mul_le_mul_left T hpow
  have hTN2 : T * T ≤ 2 * N := by
    rw [hNdef]; nlinarith [pow_succ 2 L]
  have hTN : T ≤ N := Nat.le_mul_of_pos_right T (by positivity)
  have hN0 : 0 < N := by omega
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN0
  have hNTr : (N : ℝ) ≤ (T : ℝ) * T := by exact_mod_cast hNT
  have hTN2r : (T : ℝ) * T ≤ 2 * N := by exact_mod_cast hTN2
  -- `√N ≤ t` and `t ≤ 3 √N`
  have hsqN : Real.sqrt N ≤ t := by
    rw [Real.sqrt_le_left htpos.le]; nlinarith [(Nat.cast_nonneg T : (0 : ℝ) ≤ T)]
  have hsqN0 : 0 < Real.sqrt N := Real.sqrt_pos.mpr (by linarith)
  have hsqNsq : Real.sqrt N ^ 2 = N := Real.sq_sqrt (by linarith)
  have ht3 : t ≤ 3 * Real.sqrt N := by
    have h1 : t ≤ 2 * T := by
      have : (1 : ℝ) ≤ T := by exact_mod_cast hT1
      linarith
    nlinarith [(Nat.cast_nonneg T : (0 : ℝ) ≤ T)]
  have hz := Zeta0EqZeta (N := N) hN0 (s := s) (by rw [hsre]; linarith) hs1
  rw [← hz]
  unfold riemannZeta0
  rw [range_sum_eq s hs0 N T hTN]
  set A := ∑ n ∈ Finset.Icc 1 T, ((n : ℝ) : ℂ) ^ (-s)
  set B := ∑ n ∈ Finset.Ioc T N, ((n : ℝ) : ℂ) ^ (-s) with hB
  set E1 := (-(N : ℂ) ^ (1 - s)) / (1 - s) with hE1
  set E2 := (-(N : ℂ) ^ (-s)) / 2 with hE2
  set J := ∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ (s + 1) with hJ
  have hsplit : A + B + E1 + E2 + s * J - A = B + E1 + E2 + s * J := by ring
  rw [hsplit]
  -- the middle range
  have hBb : ‖B‖ ≤ 16 * Real.pi := by
    have := middle_bound t σ hσ0 htpos T hT1 htT L
    rw [← hNdef] at this
    refine this.trans ?_
    rw [div_le_iff₀ htpos]
    nlinarith
  -- `N^{1-s}/(1-s)`
  have hE1b : ‖E1‖ ≤ 1 := by
    rw [hE1, norm_div, norm_neg, Complex.norm_natCast_cpow_of_pos hN0]
    have hre : (1 - s).re = 1 - σ := by simp [hsre]
    rw [hre]
    have hden : t ≤ ‖1 - s‖ := by
      have := Complex.abs_im_le_norm (1 - s)
      have e : (1 - s).im = -t := by simp [hsim]
      rw [e, abs_neg, abs_of_pos htpos] at this
      exact this
    have hnum : (N : ℝ) ^ (1 - σ) ≤ Real.sqrt N := by
      rw [Real.sqrt_eq_rpow]
      exact Real.rpow_le_rpow_of_exponent_le hNr (by linarith)
    rw [div_le_one (by linarith)]
    linarith
  have hE2b : ‖E2‖ ≤ 1 / 2 := by
    rw [hE2, norm_div, norm_neg, Complex.norm_natCast_cpow_of_pos hN0]
    have hre : (-s).re = -σ := by simp [hsre]
    rw [hre]
    have : (N : ℝ) ^ (-σ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hNr (by linarith)
    simp only [Complex.norm_ofNat]
    linarith
  have hJb : ‖s * J‖ ≤ 6 := by
    have hI := integral_bound s (by rw [hsre]; linarith) N hN0
    rw [hsre] at hI
    have hsn : ‖s‖ ≤ 2 * t := by
      have h1 : ‖s‖ ≤ ‖(σ : ℂ)‖ + ‖(t : ℂ) * I‖ := norm_add_le _ _
      rw [Complex.norm_real, norm_mul, Complex.norm_real, Complex.norm_I, mul_one,
        Real.norm_of_nonneg (by linarith), Real.norm_of_nonneg htpos.le] at h1
      linarith
    have hNs : (N : ℝ) ^ (-σ) ≤ 1 / Real.sqrt N := by
      have : (N : ℝ) ^ (-σ) ≤ (N : ℝ) ^ (-(1 / 2 : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le hNr (by linarith)
      refine this.trans (le_of_eq ?_)
      rw [Real.rpow_neg (by linarith), Real.sqrt_eq_rpow, one_div]; norm_num
    have hNs0 : 0 ≤ (N : ℝ) ^ (-σ) := Real.rpow_nonneg (by linarith) _
    have h2 : (N : ℝ) ^ (-σ) / (2 * σ) ≤ 1 / Real.sqrt N := by
      rw [div_le_iff₀ (by linarith)]
      have : 0 ≤ 1 / Real.sqrt N := by positivity
      nlinarith
    rw [norm_mul]
    calc ‖s‖ * ‖J‖ ≤ (2 * t) * (1 / Real.sqrt N) := by
          gcongr
          exact hI.trans h2
      _ ≤ 6 := by
          rw [mul_one_div, div_le_iff₀ hsqN0]; linarith
  calc ‖B + E1 + E2 + s * J‖ ≤ ‖B‖ + ‖E1‖ + ‖E2‖ + ‖s * J‖ := by
        refine (norm_add_le _ _).trans ?_
        gcongr
        refine (norm_add_le _ _).trans ?_
        gcongr
        exact norm_add_le _ _
    _ ≤ 16 * Real.pi + 10 := by linarith

end GuthMaynard.CitedZeros.Rich.PartY
end

section
open Complex Filter Topology Set
namespace GuthMaynard.CitedZeros.Rich
alias approx_formula := GuthMaynard.CitedZeros.Rich.PartY.approx_formula

end GuthMaynard.CitedZeros.Rich
end

section
open Complex Filter Topology Set
namespace GuthMaynard.CitedZeros.Rich.PartX
open GuthMaynard.CitedZeros.Rich
/-! ## `small_t` -/
theorem small_t (t₁ : ℝ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ σ t : ℝ, 1 / 2 ≤ σ → σ ≤ 1 → 2 ≤ |t| → |t| ≤ t₁ →
    ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ≤ C := by
  set K : Set (ℝ × ℝ) := (Icc (1 / 2) 1 ×ˢ Icc (-t₁) t₁) ∩ {p | 2 ≤ |p.2|} with hK
  have hKc : IsCompact K := (isCompact_Icc.prod isCompact_Icc).inter_right
    (isClosed_le continuous_const (continuous_abs.comp continuous_snd))
  have hcont : ContinuousOn (fun p : ℝ × ℝ => riemannZeta ((p.1 : ℂ) + (p.2 : ℂ) * I)) K := by
    intro p hp
    apply ContinuousAt.continuousWithinAt
    have hne : (p.1 : ℂ) + (p.2 : ℂ) * I ≠ 1 := by
      intro h
      have h1 := congrArg Complex.im h
      simp at h1
      have h2 : 2 ≤ |p.2| := hp.2
      rw [h1] at h2; norm_num at h2
    exact ContinuousAt.comp (g := riemannZeta) (differentiableAt_riemannZeta hne).continuousAt
      (by fun_prop)
  obtain ⟨C, hC⟩ := hKc.exists_bound_of_continuousOn hcont
  refine ⟨max C 0, le_max_right _ _, fun σ t h1 h2 h3 h4 => ?_⟩
  have hmem : (σ, t) ∈ K := ⟨⟨⟨h1, h2⟩, abs_le.mp h4⟩, h3⟩
  exact (hC _ hmem).trans (le_max_left _ _)

end GuthMaynard.CitedZeros.Rich.PartX
end

section
open Complex Filter Topology Set
namespace GuthMaynard.CitedZeros.Rich
alias small_t := GuthMaynard.CitedZeros.Rich.PartX.small_t

end GuthMaynard.CitedZeros.Rich
end

section
open Complex Filter Topology Set
namespace GuthMaynard.CitedZeros.Rich.PartX
open GuthMaynard.CitedZeros.Rich
/-! ## `zeta_norm_neg` -/
theorem zeta_norm_neg (σ t : ℝ) :
    ‖riemannZeta ((σ : ℂ) + ((-t : ℝ) : ℂ) * I)‖ = ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ := by
  have h : (σ : ℂ) + ((-t : ℝ) : ℂ) * I = (starRingEnd ℂ) ((σ : ℂ) + (t : ℂ) * I) := by
    apply Complex.ext <;> simp
  rw [h, riemannZeta_conj, Complex.norm_conj]

end GuthMaynard.CitedZeros.Rich.PartX
end

section
open Complex Filter Topology Set
namespace GuthMaynard.CitedZeros.Rich
alias zeta_norm_neg := GuthMaynard.CitedZeros.Rich.PartX.zeta_norm_neg

/-! ## Assembly (no `sorry` below) -/
/-- The bound for `t ≥ t₁`, `t > 0`. -/
theorem large_t : ∃ A B t₁ : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ 3 ≤ t₁ ∧ ∀ σ t : ℝ, 1 / 2 ≤ σ → σ ≤ 1 → t₁ ≤ t →
    ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ≤
      A * t ^ (B * (1 - σ) ^ (3 / 2 : ℝ)) * Real.log t ^ (2 / 3 : ℝ) := by
  obtain ⟨K, t₀, hK, happ⟩ := approx_formula
  obtain ⟨B, C, hB, hC, hexp⟩ := exp_sum_bound
  refine ⟨K + 1 + 9.463 * C, B, max t₀ 3, by positivity, hB, le_max_right _ _,
    fun σ t hσ0 hσ1 ht => ?_⟩
  have ht0 : t₀ ≤ t := le_trans (le_max_left _ _) ht
  have ht3 : (3 : ℝ) ≤ t := le_trans (le_max_right _ _) ht
  have htpos : 0 < t := by linarith
  have hlog : 1 ≤ Real.log t := by
    rw [Real.le_log_iff_exp_le htpos]
    exact (Real.exp_one_lt_d9.le.trans (by norm_num)).trans ht3
  have hlog0 : 0 < Real.log t := by linarith
  set E : ℝ := t ^ (B * (1 - σ) ^ (3 / 2 : ℝ)) with hE
  set P : ℝ := Real.log t ^ (2 / 3 : ℝ) with hP
  have hE1 : 1 ≤ E := Real.one_le_rpow (by linarith) (by
    have : 0 ≤ (1 - σ) ^ (3 / 2 : ℝ) := Real.rpow_nonneg (by linarith) _
    positivity)
  have hP1 : 1 ≤ P := Real.one_le_rpow hlog (by norm_num)
  have hEexp : Real.exp (B * (1 - σ) ^ (3 / 2 : ℝ) * Real.log t) = E := by
    rw [hE, Real.rpow_def_of_pos htpos]; ring_nf
  have h1 := happ t ht0 σ hσ0 hσ1
  have h2 := dyadic_sum t σ (by linarith) hσ0 hσ1
  have h3 := hexp (Real.log t) hlog σ hσ0 hσ1 (⌊Real.log t / Real.log 2⌋₊ + 1)
  rw [hEexp] at h3
  have hsum : ‖∑ n ∈ Finset.Icc 1 ⌊t⌋₊, ((n : ℝ) : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I))‖ ≤
      1 + 9.463 * (C * E * P) := h2.trans (by gcongr)
  have htri : ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ≤ K + (1 + 9.463 * (C * E * P)) := by
    calc ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖
        ≤ ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I) -
            ∑ n ∈ Finset.Icc 1 ⌊t⌋₊, ((n : ℝ) : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I))‖ +
          ‖∑ n ∈ Finset.Icc 1 ⌊t⌋₊, ((n : ℝ) : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I))‖ :=
          norm_le_norm_sub_add _ _
      _ ≤ K + (1 + 9.463 * (C * E * P)) := add_le_add h1 hsum
  have hEP : 1 ≤ E * P := by nlinarith
  calc ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ≤ K + (1 + 9.463 * (C * E * P)) := htri
    _ ≤ (K + 1 + 9.463 * C) * E * P := by nlinarith

/-- **Richert's bound** (Ford (1.1)), in the form of the published statement. -/
theorem richert_zeta_bound_dev :
    ∃ A B : ℝ, ∀ σ t : ℝ, 1 / 2 ≤ σ → σ ≤ 1 → 2 ≤ |t| →
      ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
        A * |t| ^ (B * (1 - σ) ^ (3 / 2 : ℝ)) * Real.log |t| ^ (2 / 3 : ℝ) := by
  obtain ⟨A, B, t₁, hA, hB, ht₁, hlarge⟩ := large_t
  obtain ⟨C₀, hC₀, hsmall⟩ := small_t t₁
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set c : ℝ := (Real.log 2) ^ (2 / 3 : ℝ) with hc
  have hc0 : 0 < c := Real.rpow_pos_of_pos hl2 _
  refine ⟨A + C₀ / c, B, fun σ t hσ0 hσ1 ht => ?_⟩
  have hTpos : 0 < |t| := by linarith
  have hE1 : 1 ≤ |t| ^ (B * (1 - σ) ^ (3 / 2 : ℝ)) := by
    have : 0 ≤ (1 - σ) ^ (3 / 2 : ℝ) := Real.rpow_nonneg (by linarith) _
    exact Real.one_le_rpow (by linarith) (by positivity)
  have hlogt : Real.log 2 ≤ Real.log |t| := Real.log_le_log (by norm_num) ht
  have hPge : c ≤ Real.log |t| ^ (2 / 3 : ℝ) :=
    Real.rpow_le_rpow hl2.le hlogt (by norm_num)
  set E := |t| ^ (B * (1 - σ) ^ (3 / 2 : ℝ)) with hE
  set P := Real.log |t| ^ (2 / 3 : ℝ) with hP
  have hE0 : 0 ≤ E := by linarith
  have hP0 : 0 ≤ P := hc0.le.trans hPge
  have hCc0 : 0 ≤ C₀ / c := div_nonneg hC₀ hc0.le
  -- the bound for the positive ordinate `|t|`
  have hpos : ‖riemannZeta ((σ : ℂ) + ((|t| : ℝ) : ℂ) * Complex.I)‖ ≤ (A + C₀ / c) * E * P := by
    by_cases hbig : t₁ ≤ |t|
    · have h := hlarge σ |t| hσ0 hσ1 hbig
      refine h.trans ?_
      have : 0 ≤ C₀ / c * E * P := mul_nonneg (mul_nonneg hCc0 hE0) hP0
      nlinarith
    · push Not at hbig
      have h := hsmall σ |t| hσ0 hσ1 (by rw [abs_abs]; exact ht) (by rw [abs_abs]; exact hbig.le)
      have hCc : C₀ ≤ C₀ / c * P := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hc0]
        exact mul_le_mul_of_nonneg_left hPge hC₀
      have : C₀ / c * P ≤ C₀ / c * E * P := by
        have h0 : 0 ≤ C₀ / c * P := mul_nonneg hCc0 hP0
        nlinarith
      have : 0 ≤ A * E * P := mul_nonneg (mul_nonneg hA hE0) hP0
      nlinarith
  rcases le_or_gt 0 t with h0 | h0
  · rw [abs_of_nonneg h0] at hpos; exact hpos
  · rw [abs_of_neg h0, zeta_norm_neg σ t] at hpos; exact hpos

end GuthMaynard.CitedZeros.Rich
end

section
open Complex Filter Topology Set
open GuthMaynard
open GuthMaynard.CitedZeros
open GuthMaynard.CitedZeros.Rich
theorem solution :
    ∃ A B : ℝ, ∀ σ t : ℝ, 1 / 2 ≤ σ → σ ≤ 1 → 2 ≤ |t| →
      ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
        A * |t| ^ (B * (1 - σ) ^ (3 / 2 : ℝ)) * Real.log |t| ^ (2 / 3 : ℝ) := by
  exact GuthMaynard.CitedZeros.Rich.richert_zeta_bound_dev
end
