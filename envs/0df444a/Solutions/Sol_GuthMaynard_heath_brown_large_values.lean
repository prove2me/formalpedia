-- Prove2me | solution 1 for GuthMaynard.heath_brown_large_values
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-05T22:20:42.384984+00:00
-- url     : https://prove2.me/submissions/a547b4ad-0500-43c9-9e9a-13de375f5cbc

import Mathlib
import Theorems.Thm_GuthMaynard_kerr_double_sum_le
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

/-! ## Part C -/

/-! ## Part Q -/

/-! ## Part P -/

/-! ## Part D -/

/-! ## Part T -/
theorem thm16 : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ (A : Finset ℝ) (T : ℝ) (N : ℕ),
    IsSeparated 1 A → (∀ x ∈ A, ∀ y ∈ A, |x - y| ≤ T) → 2 ≤ T → 1 ≤ N →
    S A N ≤ C * T ^ ε * ((A.card : ℝ) ^ 2 + N * A.card +
      T ^ (1 / 2 : ℝ) * (A.card : ℝ) ^ (5 / 4 : ℝ)) :=
  GuthMaynard.kerr_double_sum_le

end
end GuthMaynard.CitedLV.HB
end

section
open Finset Complex
namespace GuthMaynard.CitedLV.HB.PartF
noncomputable section
/-!
# Heath-Brown large values, Part T: `thm16` and `heath_brown_large_values`

Kerr's Theorem 16 for `γ = 1_A` from the Blueprint stubs `dual`, `square`, `mono`, `mvt_bound`:

* `case1`: if `X³ ≥ 3·10⁸ T²` then `S(X) ≪ T^ε (R² + XR)` (`dual` at `M₁ = ⌈64(T/X+1)⌉`, `square`
  at `M₂ = 256 M₁²`, `mono` from `M₂` up to `X`, then absorb `s ≤ a√s + b`; `mvt_bound` if `X > T`).
* `bound47`: for every `N`, `S(N) ≪ T^ε (R² + NR + (T/N) R^{3/2} + T^{1/2} R^{5/4})`
  (`dual`, `square`, `mono` up to `Y = max(64 M₂, ⌈700 T^{2/3}⌉)`, `case1` at `Y`).
* `thm16`: Kerr's U-trick: `mono` from `N` up to `X = max(64N, ⌈T^{1/2} R^{1/4}⌉)` and `bound47` at `X`.
* `heath_brown_large_values`: `majorant` with `|a_n| ≤ T^δ (2N)^{1/2} n^{-1/2}` and `thm16`.

The real-arithmetic steps are isolated in standalone lemmas; `R^{1/4} = u`, `T^{1/6} = v` turn the
fractional powers into polynomials.
-/
/-! ### Elementary facts -/

lemma Q_smul (A : Finset ℝ) (F : ℝ → ℂ) (z : ℂ) :
    Q A (fun t => z * F t) = ‖z‖ ^ 2 * Q A F := by
  unfold Q; simp [mul_pow, Finset.mul_sum]

/-! ### Real-arithmetic lemmas -/

/-! ### Case 1 -/

/-! ### The bound (47') -/

/-! ### The published statement -/
/-- The published statement `GuthMaynard.heath_brown_large_values`, verbatim. -/
theorem heath_brown_large_values :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T → ∀ (N : ℕ), 1 ≤ N →
      ∀ a : ℕ → ℂ, (∀ n, ‖a n‖ ≤ T ^ δ) → ∀ (P : Finset ℝ) (c : ℝ), IsSeparated 1 P →
      (∀ t ∈ P, t ∈ Set.Icc c (c + T)) →
      ∑ t₁ ∈ P, ∑ t₂ ∈ P, ‖∑ n ∈ Finset.Icc N (2 * N), a n * (n : ℂ) ^ (((t₁ - t₂ : ℝ) : ℂ) * Complex.I)‖ ^ 2 ≤
        T ^ ε * ((P.card : ℝ) ^ 2 * N + (P.card : ℝ) * (N : ℝ) ^ 2 +
          (P.card : ℝ) ^ (5 / 4 : ℝ) * T ^ (1 / 2 : ℝ) * N) := by
  intro ε hε
  obtain ⟨C, hC, h16⟩ := GuthMaynard.CitedLV.HB.thm16 (ε / 3) (by positivity)
  refine ⟨ε / 6, by positivity, max 2 ((2 * C) ^ (3 / ε)), ?_⟩
  intro T hT N hN a ha P c hsep hP
  have hT2 : 2 ≤ T := le_trans (le_max_left _ _) hT
  have hT0 : 0 < T := by linarith
  have hdiam : ∀ x ∈ P, ∀ y ∈ P, |x - y| ≤ T := by
    intro x hx y hy
    have h1 := hP x hx
    have h2 := hP y hy
    rw [Set.mem_Icc] at h1 h2
    rw [abs_le]; constructor <;> linarith
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  set K : ℝ := T ^ (ε / 6) * Real.sqrt (2 * N) with hKdef
  have hmaj := GuthMaynard.CitedLV.HB.majorant P N (2 * N) hN a
    (fun n => K * (n : ℝ) ^ (-(1 / 2 : ℝ))) (by
      intro n hn
      have hn' := Finset.mem_Icc.1 hn
      have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
      have hsq : (n : ℝ) ^ (1 / 2 : ℝ) ≤ Real.sqrt (2 * N) := by
        rw [← Real.sqrt_eq_rpow]
        apply Real.sqrt_le_sqrt
        exact_mod_cast hn'.2
      have hpos : 0 < (n : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hn0 _
      have h1 : 1 ≤ Real.sqrt (2 * N) * (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
        rw [Real.rpow_neg hn0.le, ← div_eq_mul_inv, one_le_div hpos]
        exact hsq
      have hTd : 0 ≤ T ^ (ε / 6) := by positivity
      calc ‖a n‖ ≤ T ^ (ε / 6) := ha n
        _ = T ^ (ε / 6) * 1 := by ring
        _ ≤ T ^ (ε / 6) * (Real.sqrt (2 * N) * (n : ℝ) ^ (-(1 / 2 : ℝ))) :=
            mul_le_mul_of_nonneg_left h1 hTd
        _ = _ := by rw [hKdef]; ring)
  have e : D (fun n => (((K * (n : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ)) : ℂ)) N (2 * N) =
      fun t => (K : ℂ) * D w N (2 * N) t := by
    funext t
    unfold D w
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    push_cast; ring
  rw [e, Q_smul, Complex.norm_real, Real.norm_eq_abs, sq_abs] at hmaj
  have hK2 : K ^ 2 = T ^ (ε / 3) * (2 * N) := by
    rw [hKdef, mul_pow, Real.sq_sqrt (by positivity), ← Real.rpow_natCast,
      ← Real.rpow_mul hT0.le]
    congr 2; push_cast; ring
  have h := h16 P T N hsep hdiam hT2 hN
  have hCT : 2 * C ≤ T ^ (ε / 3) := by
    have h1 : (2 * C) ^ (3 / ε) ≤ T := le_trans (le_max_right _ _) hT
    have h2 := Real.rpow_le_rpow (by positivity) h1 (show 0 ≤ ε / 3 by positivity)
    rw [← Real.rpow_mul (by positivity)] at h2
    have e3 : 3 / ε * (ε / 3) = 1 := by field_simp
    rw [e3, Real.rpow_one] at h2
    exact h2
  have hTT : T ^ (ε / 3) * (T ^ (ε / 3) * T ^ (ε / 3)) = T ^ ε := by
    rw [← Real.rpow_add hT0, ← Real.rpow_add hT0]; ring_nf
  have hLHS : (∑ t₁ ∈ P, ∑ t₂ ∈ P,
      ‖∑ n ∈ Finset.Icc N (2 * N), a n * (n : ℂ) ^ (((t₁ - t₂ : ℝ) : ℂ) * Complex.I)‖ ^ 2) =
      Q P (D a N (2 * N)) := rfl
  rw [hLHS]
  set Gf := (P.card : ℝ) ^ 2 + N * P.card + T ^ (1 / 2 : ℝ) * (P.card : ℝ) ^ (5 / 4 : ℝ) with hGf
  have hG0 : 0 ≤ Gf := by positivity
  have hτ : 0 ≤ T ^ (ε / 3) := by positivity
  have hS : S P N ≤ C * T ^ (ε / 3) * Gf := h
  calc Q P (D a N (2 * N)) ≤ K ^ 2 * Q P (D w N (2 * N)) := hmaj
    _ ≤ T ^ (ε / 3) * (2 * N) * (C * T ^ (ε / 3) * Gf) := by
        rw [hK2]; exact mul_le_mul_of_nonneg_left hS (by positivity)
    _ = (2 * C) * (T ^ (ε / 3) * T ^ (ε / 3)) * (N * Gf) := by ring
    _ ≤ T ^ (ε / 3) * (T ^ (ε / 3) * T ^ (ε / 3)) * (N * Gf) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_right hCT (by positivity)
    _ = _ := by rw [hTT, hGf]; ring

end
end GuthMaynard.CitedLV.HB.PartF
end

section
open Finset Complex
namespace GuthMaynard.CitedLV.HB
noncomputable section
alias heath_brown_large_values := GuthMaynard.CitedLV.HB.PartF.heath_brown_large_values

end
end GuthMaynard.CitedLV.HB
end


open GuthMaynard in
theorem solution :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T → ∀ (N : ℕ), 1 ≤ N →
      ∀ a : ℕ → ℂ, (∀ n, ‖a n‖ ≤ T ^ δ) → ∀ (P : Finset ℝ) (c : ℝ), IsSeparated 1 P →
      (∀ t ∈ P, t ∈ Set.Icc c (c + T)) →
      ∑ t₁ ∈ P, ∑ t₂ ∈ P, ‖∑ n ∈ Finset.Icc N (2 * N), a n * (n : ℂ) ^ (((t₁ - t₂ : ℝ) : ℂ) * Complex.I)‖ ^ 2 ≤
        T ^ ε * ((P.card : ℝ) ^ 2 * N + (P.card : ℝ) * (N : ℝ) ^ 2 +
          (P.card : ℝ) ^ (5 / 4 : ℝ) * T ^ (1 / 2 : ℝ) * N) :=
  GuthMaynard.CitedLV.HB.heath_brown_large_values
