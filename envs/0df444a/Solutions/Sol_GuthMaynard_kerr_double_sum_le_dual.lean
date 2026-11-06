-- Prove2me | solution 1 for GuthMaynard.kerr_double_sum_le_dual
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-05T22:20:43.218408+00:00
-- url     : https://prove2.me/submissions/f2dfb451-4b6d-4618-9076-7c494c6b87f5

import Mathlib
import Theorems.Thm_GuthMaynard_kerr_double_sum_mono
import Theorems.Thm_GuthMaynard_norm_dyadic_sum_cpow_le
import Theorems.Thm_GuthMaynard_norm_dyadic_sum_cpow_le_dual_sum
import Definitions.Def_GuthMaynard
section
/-!
# Blueprint: Huxley 1972 (2.9), the Montgomery–Halász–Huxley large values estimate

Route (elementary, no ζ):
* `partial_sum_cpow_le` (van der Corput second-derivative test via Kusmin–Landau):
  `|∑_{m ≤ c} m^{-it}| ≪ |t|^{1/2} log(|t|+2)` for `c ≤ 11|t|+2`.
* `block_sum_sub_integral_le` (sum vs integral on a dyadic block where the phase is slow).
* `kernel_bound`: the tent-weighted kernel `K(s) = ∑ w(m) m^{-s}` is
  `≪ N/t² + |t|^{1/2} log(|t|+2) + log(N+2)`.
* `halasz_ineq`, `sum_inv_sq_le_of_separated`, `card_le_of_separated`, `card_le_of_halasz`:
  Halász–Montgomery, giving `R ≪ GN/V²` when `V² ≫ G (T^{1/2} log(T+2) + log(N+2))`.
* `huxley_main`: subdivision of the `t`-range into pieces of length `T₀`.
-/

open Finset Complex

namespace GuthMaynard.CitedLV

noncomputable section

/-! ## Part V: van der Corput partial sums -/

/-! ## Part B: sum versus integral on a block with slowly varying phase -/

/-! ## Part K: the kernel bound -/

/-! ## Part H: Halász–Montgomery and subdivision -/

end

end GuthMaynard.CitedLV
end

section
open Finset Complex

namespace GuthMaynard.CitedLV.PartH

noncomputable section

/-! ## Helpers -/

/-! ## Targets -/

/-- Corrected form, with `r ∈ P`. -/
theorem sum_inv_sq_le_of_separated {ι : Type*} [DecidableEq ι] (P : Finset ι) (t : ι → ℝ)
    (ht : ∀ r ∈ P, ∀ q ∈ P, r ≠ q → 1 ≤ |t r - t q|) (r : ι) (hr : r ∈ P) :
    ∑ q ∈ P.erase r, 1 / (t r - t q) ^ 2 ≤ 4 := by
  set E := P.erase r with hE
  let k : ι → ℕ := fun q => ⌊|t r - t q|⌋₊
  let φ : ι → Bool × ℕ := fun q => (decide (t q < t r), k q)
  have hk1 : ∀ q ∈ E, 1 ≤ k q := fun q hq => by
    have := ht r hr q (mem_of_mem_erase hq) (ne_of_mem_erase hq).symm
    exact Nat.le_floor (by simpa using this)
  have hinj : Set.InjOn φ E := by
    intro q hq q' hq' h
    simp only [φ, Prod.mk.injEq, decide_eq_decide] at h
    obtain ⟨hs, hkk⟩ := h
    by_contra hne
    have hsep := ht q (mem_of_mem_erase hq) q' (mem_of_mem_erase hq') hne
    have h1 : (k q : ℝ) ≤ |t r - t q| := Nat.floor_le (abs_nonneg _)
    have h2 : |t r - t q| < k q + 1 := Nat.lt_floor_add_one _
    have h3 : (k q' : ℝ) ≤ |t r - t q'| := Nat.floor_le (abs_nonneg _)
    have h4 : |t r - t q'| < k q' + 1 := Nat.lt_floor_add_one _
    have e : (k q : ℝ) = k q' := by exact_mod_cast hkk
    have hlt : |t q - t q'| < 1 := by
      by_cases hq1 : t q < t r
      · have hq2 : t q' < t r := hs.1 hq1
        have ea := abs_of_pos (by linarith : 0 < t r - t q)
        have eb := abs_of_pos (by linarith : 0 < t r - t q')
        rw [abs_lt]; constructor <;> linarith
      · have hq2 : ¬ t q' < t r := fun h => hq1 (hs.2 h)
        rw [not_lt] at hq1 hq2
        have ea := abs_of_nonpos (by linarith : t r - t q ≤ 0)
        have eb := abs_of_nonpos (by linarith : t r - t q' ≤ 0)
        rw [abs_lt]; constructor <;> linarith
    linarith
  have hS : ∀ q ∈ E, 1 / (t r - t q) ^ 2 ≤ 1 / ((k q : ℝ)) ^ 2 := by
    intro q hq
    have hk := hk1 q hq
    have hpos : (0 : ℝ) < k q := by exact_mod_cast hk
    apply one_div_le_one_div_of_le (by positivity)
    have := Nat.floor_le (abs_nonneg (t r - t q))
    rw [← sq_abs (t r - t q)]
    exact pow_le_pow_left₀ hpos.le this 2
  set M := (E.image k).sup id + 1 with hM
  calc ∑ q ∈ E, 1 / (t r - t q) ^ 2 ≤ ∑ q ∈ E, 1 / ((k q : ℝ)) ^ 2 := sum_le_sum hS
    _ = ∑ x ∈ E.image φ, 1 / ((x.2 : ℝ)) ^ 2 := (sum_image (f := fun x : Bool × ℕ => 1 / ((x.2 : ℝ)) ^ 2) hinj).symm
    _ ≤ ∑ x ∈ (univ : Finset Bool) ×ˢ Ioo 0 M, 1 / ((x.2 : ℝ)) ^ 2 := by
        apply sum_le_sum_of_subset_of_nonneg
        · intro x hx
          obtain ⟨q, hq, rfl⟩ := mem_image.1 hx
          simp only [mem_product, mem_univ, true_and, mem_Ioo, φ]
          refine ⟨hk1 q hq, ?_⟩
          have : k q ≤ (E.image k).sup id := Finset.le_sup (f := id) (mem_image_of_mem k hq)
          omega
        · intro _ _ _; positivity
    _ = 2 * ∑ i ∈ Ioo 0 M, ((i : ℝ) ^ 2)⁻¹ := by
        rw [sum_product]; simp [two_mul]
    _ ≤ 2 * 2 := by
        have := sum_Ioo_inv_sq_le (α := ℝ) 0 M
        norm_num at this
        linarith
    _ = 4 := by norm_num

end

end GuthMaynard.CitedLV.PartH
end

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
/-- The level-`k`, index-`m` dyadic block of `a` (offsets from `L`). -/
def blk (a : ℕ → ℂ) (L k m : ℕ) : ℕ → ℂ := fun n => if (n - L) / 2 ^ k = m then a n else 0

lemma mem_piece (p q L U s n : ℕ) (hp : 0 < p) (hqs : q * p ≤ s) (hs : L + s ≤ U + 1) :
    (L + q / 2 * 2 * p ≤ n ∧ n < L + q * p) ↔
      ((L ≤ n ∧ n ≤ U) ∧ (n - L) / p = q / 2 * 2 ∧ q % 2 = 1) := by
  have hd := Nat.div_add_mod q 2
  have hm := Nat.mod_lt (n - L) hp
  have hd2 := Nat.div_add_mod (n - L) p
  rcases Nat.mod_two_eq_zero_or_one q with h | h
  · have hq : q / 2 * 2 = q := by omega
    rw [hq]
    constructor
    · intro h'; omega
    · intro h'; omega
  · have hq : q * p = q / 2 * 2 * p + p := by
      conv_lhs => rw [show q = q / 2 * 2 + 1 by omega]
      ring
    rw [hq] at hqs ⊢
    generalize q / 2 * 2 = r at *
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨⟨by omega, by omega⟩, ?_, h⟩
      apply Nat.div_eq_of_lt_le
      · omega
      · rw [add_mul, one_mul]; omega
    · rintro ⟨⟨h1, h2⟩, h3, -⟩
      rw [h3] at hd2
      have : p * r = r * p := mul_comm _ _
      omega

lemma sk_succ (s k : ℕ) : s / 2 ^ (k + 1) * 2 ^ (k + 1) = s / 2 ^ k / 2 * 2 * 2 ^ k := by
  rw [Nat.div_div_eq_div_mul, ← pow_succ, pow_succ]; ring

lemma sk_mono (s k : ℕ) : s / 2 ^ (k + 1) * 2 ^ (k + 1) ≤ s / 2 ^ k * 2 ^ k := by
  rw [sk_succ]
  exact Nat.mul_le_mul_right _ (Nat.div_mul_le_self _ _)

lemma piece (a : ℕ → ℂ) (L U s k : ℕ) (u : ℝ) (hs : L + s ≤ U + 1) :
    ∑ n ∈ Finset.Ico (L + s / 2 ^ (k + 1) * 2 ^ (k + 1)) (L + s / 2 ^ k * 2 ^ k),
      a n * (n : ℂ) ^ ((u : ℂ) * I) =
    if (s / 2 ^ k) % 2 = 1 then D (blk a L k (s / 2 ^ k / 2 * 2)) L U u else 0 := by
  have hp : 0 < 2 ^ k := by positivity
  have hqs : s / 2 ^ k * 2 ^ k ≤ s := Nat.div_mul_le_self _ _
  have hset : Finset.Ico (L + s / 2 ^ (k + 1) * 2 ^ (k + 1)) (L + s / 2 ^ k * 2 ^ k) =
      (Finset.Icc L U).filter (fun n => (n - L) / 2 ^ k = s / 2 ^ k / 2 * 2 ∧ (s / 2 ^ k) % 2 = 1) := by
    ext n
    rw [Finset.mem_Ico, Finset.mem_filter, Finset.mem_Icc, sk_succ]
    exact mem_piece _ _ L U s n hp hqs hs
  rw [hset, Finset.sum_filter]
  split_ifs with hodd
  · unfold D blk
    refine Finset.sum_congr rfl fun n _ => ?_
    simp only [hodd, and_true]
    split_ifs <;> simp
  · simp [hodd]

lemma pref_eq (f : ℕ → ℂ) (L s K : ℕ) (hK : s < 2 ^ K) :
    ∑ n ∈ Finset.Ico L (L + s), f n = ∑ k ∈ Finset.range K,
      ∑ n ∈ Finset.Ico (L + s / 2 ^ (k + 1) * 2 ^ (k + 1)) (L + s / 2 ^ k * 2 ^ k), f n := by
  set F : ℕ → ℂ := fun k => ∑ n ∈ Finset.Ico L (L + s / 2 ^ k * 2 ^ k), f n with hF
  have h0 : F 0 = ∑ n ∈ Finset.Ico L (L + s), f n := by simp [hF]
  have hK' : F K = 0 := by simp [hF, Nat.div_eq_of_lt hK]
  rw [← h0, show F 0 = F 0 - F K by rw [hK', sub_zero], ← Finset.sum_range_sub']
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [sub_eq_iff_eq_add', hF]
  exact (Finset.sum_Ico_consecutive f (by omega) (by have := sk_mono s k; omega)).symm

lemma pref_bound (a : ℕ → ℂ) (L U s K : ℕ) (hs : L + s ≤ U + 1) (hK : s < 2 ^ K) (u : ℝ) :
    ‖∑ n ∈ Finset.Ico L (L + s), a n * (n : ℂ) ^ ((u : ℂ) * I)‖ ^ 2 ≤
      K * ∑ k ∈ Finset.range K, ∑ m ∈ Finset.range (U + 1), ‖D (blk a L k m) L U u‖ ^ 2 := by
  rw [pref_eq _ L s K hK]
  simp_rw [piece a L U s _ u hs]
  set z : ℕ → ℂ := fun k => if (s / 2 ^ k) % 2 = 1 then D (blk a L k (s / 2 ^ k / 2 * 2)) L U u else 0
  have h1 : ‖∑ k ∈ Finset.range K, z k‖ ^ 2 ≤ (∑ k ∈ Finset.range K, ‖z k‖) ^ 2 := by
    gcongr; exact norm_sum_le _ _
  have h2 := sq_sum_le_card_mul_sum_sq (s := Finset.range K) (f := fun k => ‖z k‖)
  rw [Finset.card_range] at h2
  refine h1.trans (h2.trans ?_)
  gcongr with k hk
  simp only [z]
  split_ifs with hodd
  · apply Finset.single_le_sum (f := fun m => ‖D (blk a L k m) L U u‖ ^ 2) (fun _ _ => by positivity)
    rw [Finset.mem_range]
    have : s / 2 ^ k ≤ s := Nat.div_le_self _ _
    omega
  · simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
    positivity

lemma pair_bound (a : ℕ → ℂ) (L U lo hi K : ℕ) (hL : 1 ≤ L) (hlo : L ≤ lo) (hhi : hi ≤ U) (hK : U < 2 ^ K)
    (u : ℝ) :
    ‖∑ n ∈ Finset.Icc lo hi, a n * (n : ℂ) ^ ((u : ℂ) * I)‖ ^ 2 ≤
      4 * K * ∑ k ∈ Finset.range K, ∑ m ∈ Finset.range (U + 1), ‖D (blk a L k m) L U u‖ ^ 2 := by
  set T := ∑ k ∈ Finset.range K, ∑ m ∈ Finset.range (U + 1), ‖D (blk a L k m) L U u‖ ^ 2
  have hT : 0 ≤ T := by positivity
  by_cases hlh : lo ≤ hi
  · set f : ℕ → ℂ := fun n => a n * (n : ℂ) ^ ((u : ℂ) * I)
    have e1 : Finset.Icc lo hi = Finset.Ico lo (hi + 1) := by
      ext; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
    have hsplit : ∑ n ∈ Finset.Icc lo hi, f n =
        ∑ n ∈ Finset.Ico L (L + (hi + 1 - L)), f n - ∑ n ∈ Finset.Ico L (L + (lo - L)), f n := by
      rw [e1, show L + (hi + 1 - L) = hi + 1 by omega, show L + (lo - L) = lo by omega,
        ← Finset.sum_Ico_consecutive f hlo (by omega : lo ≤ hi + 1)]
      ring
    rw [hsplit]
    have p1 : _ ≤ K * T := pref_bound a L U (hi + 1 - L) K (by omega) (by omega) u
    have p2 : _ ≤ K * T := pref_bound a L U (lo - L) K (by omega) (by omega) u
    have hn := norm_sub_le (∑ n ∈ Finset.Ico L (L + (hi + 1 - L)), f n)
      (∑ n ∈ Finset.Ico L (L + (lo - L)), f n)
    have q1 := norm_nonneg (∑ n ∈ Finset.Ico L (L + (hi + 1 - L)), f n)
    have q2 := norm_nonneg (∑ n ∈ Finset.Ico L (L + (lo - L)), f n)
    have q3 := norm_nonneg (∑ n ∈ Finset.Ico L (L + (hi + 1 - L)), f n -
      ∑ n ∈ Finset.Ico L (L + (lo - L)), f n)
    simp only [f] at hn q1 q2 q3 ⊢
    have := mul_self_le_mul_self q3 hn
    nlinarith [sq_nonneg (‖∑ n ∈ Finset.Ico L (L + (hi + 1 - L)), a n * (n : ℂ) ^ ((u : ℂ) * I)‖ -
      ‖∑ n ∈ Finset.Ico L (L + (lo - L)), a n * (n : ℂ) ^ ((u : ℂ) * I)‖)]
  · rw [Finset.Icc_eq_empty hlh]
    simp only [Finset.sum_empty, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
    positivity

lemma blocks_le (A : Finset ℝ) (a : ℕ → ℂ) (L U k M : ℕ) (hL : 1 ≤ L) :
    ∑ m ∈ Finset.range M, Q A (D (blk a L k m) L U) ≤
      Q A (D (fun n => ((‖a n‖ : ℝ) : ℂ)) L U) := by
  have hb : ∀ m, Q A (D (blk a L k m) L U) ≤ ∑ n ∈ Finset.Icc L U, ∑ n' ∈ Finset.Icc L U,
      (if (n - L) / 2 ^ k = m then ‖a n‖ else 0) * (if (n' - L) / 2 ^ k = m then ‖a n'‖ else 0) *
        g A n n' := by
    intro m
    rw [← Q_real A L U hL (fun n => if (n - L) / 2 ^ k = m then ‖a n‖ else 0)]
    apply majorant A L U hL
    intro n _
    unfold blk
    split_ifs <;> simp
  refine (Finset.sum_le_sum fun m _ => hb m).trans ?_
  rw [Q_real A L U hL (fun n => ‖a n‖), Finset.sum_comm]
  refine Finset.sum_le_sum fun n _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun n' _ => ?_
  have hg := g_nonneg A n n'
  calc _ ≤ ∑ m ∈ Finset.range M, if (n - L) / 2 ^ k = m then ‖a n‖ * ‖a n'‖ * g A n n' else 0 := by
        refine Finset.sum_le_sum fun m _ => ?_
        have := mul_nonneg (mul_nonneg (norm_nonneg (a n)) (norm_nonneg (a n'))) hg
        split_ifs <;> simp only [zero_mul, mul_zero, le_refl, this]
    _ ≤ _ := by
        rw [Finset.sum_ite_eq]
        split_ifs
        · exact le_rfl
        · positivity

lemma K_le (U : ℕ) : ((Nat.log 2 U + 1 : ℕ) : ℝ) ≤ 2 * (1 + Real.log (U + 1)) := by
  have hl0 : 0 ≤ Real.log (U + 1) := Real.log_nonneg (by linarith [(Nat.cast_nonneg U : (0 : ℝ) ≤ U)])
  rcases Nat.eq_zero_or_pos U with hU | hU
  · subst hU; simp
  · have h1 : 2 ^ Nat.log 2 U ≤ U := Nat.pow_log_le_self 2 hU.ne'
    have h2 : ((2 : ℝ) ^ Nat.log 2 U) ≤ (U : ℝ) + 1 := by
      have : ((2 ^ Nat.log 2 U : ℕ) : ℝ) ≤ U := by exact_mod_cast h1
      push_cast at this; linarith
    have h3 := Real.log_le_log (by positivity) h2
    rw [Real.log_pow] at h3
    have h4 := Real.log_two_gt_d9
    have h5 : (0 : ℝ) ≤ Nat.log 2 U := Nat.cast_nonneg _
    push_cast
    nlinarith

theorem completion : ∃ C : ℝ, 0 < C ∧ ∀ (A : Finset ℝ) (L U : ℕ), 1 ≤ L → ∀ (a : ℕ → ℂ)
    (lo hi : ℝ → ℝ → ℕ), (∀ x ∈ A, ∀ y ∈ A, L ≤ lo x y ∧ hi x y ≤ U) →
    ∑ x ∈ A, ∑ y ∈ A, ‖∑ n ∈ Finset.Icc (lo x y) (hi x y), a n * (n : ℂ) ^ (((x - y : ℝ) : ℂ) * I)‖ ^ 2
      ≤ C * (1 + Real.log (U + 1)) ^ 2 * Q A (D (fun n => ((‖a n‖ : ℝ) : ℂ)) L U) := by
  refine ⟨16, by norm_num, ?_⟩
  intro A L U hL a lo hi hlohi
  set K := Nat.log 2 U + 1 with hKdef
  have hK : U < 2 ^ K := Nat.lt_pow_succ_log_self (by norm_num) U
  set B := Q A (D (fun n => ((‖a n‖ : ℝ) : ℂ)) L U)
  have hB : 0 ≤ B := by
    simp only [B, Q]; positivity
  calc _ ≤ ∑ x ∈ A, ∑ y ∈ A, 4 * K * ∑ k ∈ Finset.range K, ∑ m ∈ Finset.range (U + 1),
        ‖D (blk a L k m) L U (x - y)‖ ^ 2 := by
        refine Finset.sum_le_sum fun x hx => Finset.sum_le_sum fun y hy => ?_
        exact pair_bound a L U (lo x y) (hi x y) K hL (hlohi x hx y hy).1 (hlohi x hx y hy).2 hK (x - y)
    _ = 4 * K * ∑ k ∈ Finset.range K, ∑ m ∈ Finset.range (U + 1), Q A (D (blk a L k m) L U) := by
        simp only [Q, ← Finset.mul_sum]
        congr 1
        rw [swap4]
    _ ≤ 4 * K * ∑ k ∈ Finset.range K, B := by
        gcongr with k hk
        exact blocks_le A a L U k (U + 1) hL
    _ = 4 * (K : ℝ) ^ 2 * B := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
    _ ≤ 16 * (1 + Real.log (U + 1)) ^ 2 * B := by
        have hKl : (K : ℝ) ≤ 2 * (1 + Real.log (U + 1)) := K_le U
        have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg _
        calc 4 * (K : ℝ) ^ 2 * B ≤ 4 * (2 * (1 + Real.log (U + 1))) ^ 2 * B := by gcongr
          _ = _ := by ring

end
end GuthMaynard.CitedLV.HB.PartM
end

section
open Finset Complex
namespace GuthMaynard.CitedLV.HB
noncomputable section
alias completion := GuthMaynard.CitedLV.HB.PartM.completion

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

/-! ### The character sums -/

/-! ### The product polynomial -/

/-! ### One block -/

/-! ### `mono` -/

end
end GuthMaynard.CitedLV.HB.PartC
end

section
open Finset Complex
namespace GuthMaynard.CitedLV.HB
noncomputable section
theorem mono : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ (A : Finset ℝ) (N M : ℕ), 1 ≤ N →
    64 * N ≤ M → S A N ≤ C * (M : ℝ) ^ ε * S A M :=
  GuthMaynard.kerr_double_sum_mono

/-! ## Part Q -/

/-! ## Part P -/
theorem dyadic_pointwise : ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N → ∀ u : ℝ, 1 ≤ |u| →
    ‖∑ n ∈ Finset.Icc N (2 * N), (n : ℂ) ^ ((u : ℂ) * I)‖ ≤
      C * (N / |u| + |u| ^ (1 / 2 : ℝ) * Real.log (|u| + 2)) :=
  GuthMaynard.norm_dyadic_sum_cpow_le

/-- Kerr's Lemma 26 (van der Corput's B-process), with explicit ranges. -/
theorem bprocess : ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N → ∀ t : ℝ, 10 * N ≤ t →
    ∃ L M : ℕ, 1 ≤ L ∧ t / (8 * Real.pi * N) ≤ L ∧ (M : ℝ) ≤ t / (Real.pi * N) + 1 ∧
      ‖∑ n ∈ Finset.Icc N (2 * N), (n : ℂ) ^ ((t : ℂ) * I)‖ ≤
        C * (N / Real.sqrt t * ‖∑ m ∈ Finset.Icc L M, (m : ℂ) ^ ((t : ℂ) * I)‖ +
          N / Real.sqrt t + Real.log (N * t + 2)) :=
  GuthMaynard.norm_dyadic_sum_cpow_le_dual_sum

end
end GuthMaynard.CitedLV.HB
end

section
open Finset Complex
namespace GuthMaynard.CitedLV.HB.PartD
open GuthMaynard.CitedLV.HB
noncomputable section
/-! ## Notation and elementary facts about `Q` and `D` -/
/-- `∑_{L ≤ m ≤ U} m^{iu}`. -/
def Fsum (L U : ℕ) (u : ℝ) : ℂ := ∑ m ∈ Finset.Icc L U, (m : ℂ) ^ ((u : ℂ) * I)

lemma Q_nonneg (A : Finset ℝ) (F : ℝ → ℂ) : 0 ≤ Q A F := by
  unfold Q; positivity

lemma S_nonneg (A : Finset ℝ) (N : ℕ) : 0 ≤ S A N := Q_nonneg _ _

lemma Q_const_mul (A : Finset ℝ) (L U : ℕ) (c : ℂ) (a : ℕ → ℂ) :
    Q A (D (fun n => c * a n) L U) = ‖c‖ ^ 2 * Q A (D a L U) := by
  unfold Q D
  rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun y _ => ?_
  simp_rw [mul_assoc]; rw [← Finset.mul_sum, norm_mul, mul_pow]

lemma Q_add_le (A : Finset ℝ) (F G : ℝ → ℂ) :
    Q A (fun u => F u + G u) ≤ 2 * Q A F + 2 * Q A G := by
  unfold Q
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun x _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun y _ => ?_
  have := norm_add_le (F (x - y)) (G (x - y))
  nlinarith [norm_nonneg (F (x - y)), norm_nonneg (G (x - y)), norm_nonneg (F (x - y) + G (x - y)),
    sq_nonneg (‖F (x - y)‖ - ‖G (x - y)‖)]

lemma D_split (a : ℕ → ℂ) (L m U : ℕ) (h1 : L ≤ m + 1) (h2 : m ≤ U) (u : ℝ) :
    D a L U u = D a L m u + D a (m + 1) U u := by
  unfold D
  rw [← Finset.sum_union]
  · congr 1; ext n; simp only [Finset.mem_Icc, Finset.mem_union]; omega
  · rw [Finset.disjoint_left]; intro n h1 h2; simp only [Finset.mem_Icc] at h1 h2; omega

lemma Q_D_empty (A : Finset ℝ) (a : ℕ → ℂ) (L U : ℕ) (h : U < L) : Q A (D a L U) = 0 := by
  unfold Q D; simp [Finset.Icc_eq_empty_of_lt h]

lemma norm_w (n : ℕ) : ((‖w n‖ : ℝ) : ℂ) = w n := by
  unfold w
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)]

/-! ## One dyadic piece, and an interval of bounded ratio -/
lemma piece_bound (A : Finset ℝ) (M : ℕ) (ε' Cc Cm : ℝ) (hCc : 0 < Cc)
    (hcomp : ∀ (A : Finset ℝ) (L U : ℕ), 1 ≤ L → ∀ (a : ℕ → ℂ)
      (lo hi : ℝ → ℝ → ℕ), (∀ x ∈ A, ∀ y ∈ A, L ≤ lo x y ∧ hi x y ≤ U) →
      ∑ x ∈ A, ∑ y ∈ A, ‖∑ n ∈ Finset.Icc (lo x y) (hi x y), a n * (n : ℂ) ^ (((x - y : ℝ) : ℂ) * I)‖ ^ 2
        ≤ Cc * (1 + Real.log (U + 1)) ^ 2 * Q A (D (fun n => ((‖a n‖ : ℝ) : ℂ)) L U))
    (hmono : ∀ (A : Finset ℝ) (N M : ℕ), 1 ≤ N → 64 * N ≤ M → S A N ≤ Cm * (M : ℝ) ^ ε' * S A M)
    (K hi : ℕ) (hK : 1 ≤ K) (hKM : 64 * K ≤ M) (hhi : hi ≤ 2 * K) :
    Q A (D w K hi) ≤ Cc * (1 + Real.log (M + 1)) ^ 2 * (Cm * (M : ℝ) ^ ε' * S A M) := by
  have h := hcomp A K (2 * K) hK w (fun _ _ => K) (fun _ _ => hi) (fun _ _ _ _ => ⟨le_rfl, hhi⟩)
  simp only [norm_w] at h
  have hS : Q A (D w K (2 * K)) = S A K := rfl
  rw [hS] at h
  have hm := hmono A K M hK hKM
  have hl0 : 0 ≤ 1 + Real.log (((2 * K : ℕ) : ℝ) + 1) := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ ((2 * K : ℕ) : ℝ) + 1 by
      have := Nat.cast_nonneg (α := ℝ) (2 * K); linarith)
    linarith
  have hlog : (1 + Real.log (((2 * K : ℕ) : ℝ) + 1)) ^ 2 ≤ (1 + Real.log ((M : ℝ) + 1)) ^ 2 := by
    gcongr
    have : 2 * K ≤ M := by omega
    exact_mod_cast this
  calc Q A (D w K hi) ≤ Cc * (1 + Real.log (((2 * K : ℕ) : ℝ) + 1)) ^ 2 * S A K := h
    _ ≤ Cc * (1 + Real.log ((M : ℝ) + 1)) ^ 2 * (Cm * (M : ℝ) ^ ε' * S A M) := by
      gcongr
      exact S_nonneg A K

lemma range_bound (A : Finset ℝ) (M : ℕ) (G : ℝ) (hG : 0 ≤ G)
    (hpiece : ∀ K hi : ℕ, 1 ≤ K → 64 * K ≤ M → hi ≤ 2 * K → Q A (D w K hi) ≤ G) :
    ∀ k L U : ℕ, 1 ≤ L → U < L * 2 ^ k → 64 * U ≤ M → Q A (D w L U) ≤ 4 ^ k * G := by
  intro k
  induction k with
  | zero =>
    intro L U hL hU _
    simp only [pow_zero, mul_one] at hU
    rw [Q_D_empty A w L U hU]; simpa using hG
  | succ k ih =>
    intro L U hL hU hUM
    by_cases hUL : U < L
    · rw [Q_D_empty A w L U hUL]; positivity
    have h4 : (1 : ℝ) ≤ 4 ^ k := one_le_pow₀ (by norm_num)
    by_cases h2 : U < 2 * L
    · calc Q A (D w L U) ≤ G := hpiece L U hL (by omega) (by omega)
        _ ≤ 4 ^ (k + 1) * G := by rw [pow_succ]; nlinarith
    · push Not at h2
      have hs : D w L U = fun u => D w L (2 * L - 1) u + D w (2 * L) U u := by
        funext u
        have e : 2 * L = 2 * L - 1 + 1 := by omega
        conv_rhs => rw [e]
        exact D_split w L (2 * L - 1) U (by omega) (by omega) u
      rw [hs]
      have hU' : U < 2 * L * 2 ^ k := by
        have : L * 2 ^ (k + 1) = 2 * L * 2 ^ k := by ring
        omega
      have hA := hpiece L (2 * L - 1) hL (by omega) (by omega)
      have hB := ih (2 * L) U (by omega) hU' hUM
      calc Q A (fun u => D w L (2 * L - 1) u + D w (2 * L) U u)
          ≤ 2 * Q A (D w L (2 * L - 1)) + 2 * Q A (D w (2 * L) U) := Q_add_le _ _ _
        _ ≤ 2 * G + 2 * (4 ^ k * G) := by gcongr
        _ ≤ 4 ^ (k + 1) * G := by rw [pow_succ]; nlinarith

/-! ## The B-process bound for either sign of `u` -/
lemma norm_sum_cpow_neg (s : Finset ℕ) (u : ℝ) :
    ‖∑ n ∈ s, (n : ℂ) ^ (((-u : ℝ) : ℂ) * I)‖ = ‖∑ n ∈ s, (n : ℂ) ^ ((u : ℂ) * I)‖ := by
  have : ∑ n ∈ s, (n : ℂ) ^ (((-u : ℝ) : ℂ) * I) =
      (starRingEnd ℂ) (∑ n ∈ s, (n : ℂ) ^ ((u : ℂ) * I)) := by
    rw [map_sum]; refine Finset.sum_congr rfl fun n _ => ?_
    have e : ((-u : ℝ) : ℂ) * I = (starRingEnd ℂ) ((u : ℂ) * I) := by
      simp [map_mul, Complex.conj_ofReal, Complex.conj_I]
    rw [e, Complex.cpow_conj _ _ (by simp [Real.pi_ne_zero.symm]), Complex.conj_natCast]
  rw [this, Complex.norm_conj]

lemma bp_abs (N : ℕ) (Cb : ℝ) (Lf Mf : ℝ → ℕ)
    (hb : ∀ t : ℝ, 10 * N ≤ t → ‖Fsum N (2 * N) t‖ ≤
      Cb * (N / Real.sqrt t * ‖Fsum (Lf t) (Mf t) t‖ + N / Real.sqrt t + Real.log (N * t + 2)))
    (u : ℝ) (hu : 10 * N ≤ |u|) :
    ‖Fsum N (2 * N) u‖ ≤ Cb * (N / Real.sqrt |u| * ‖Fsum (Lf |u|) (Mf |u|) u‖ +
      N / Real.sqrt |u| + Real.log (N * |u| + 2)) := by
  have h := hb |u| hu
  rcases abs_cases u with ⟨h1, _⟩ | ⟨h1, _⟩
  · rw [h1] at h ⊢; exact h
  · have e : |u| = -u := h1
    rw [e] at h ⊢
    unfold Fsum at h ⊢
    rwa [norm_sum_cpow_neg, norm_sum_cpow_neg] at h

/-! ## The pointwise bound -/
lemma Fsum_zero (N : ℕ) : Fsum N (2 * N) 0 = ((N : ℂ) + 1) := by
  unfold Fsum
  simp only [Complex.ofReal_zero, zero_mul, Complex.cpow_zero, Finset.sum_const, Nat.card_Icc,
    nsmul_eq_mul, mul_one]
  have : 2 * N + 1 - N = N + 1 := by omega
  rw [this]; push_cast; ring

lemma pointwise (N : ℕ) (hN : 1 ≤ N) (T Cd Cb : ℝ) (hCd : 0 < Cd) (hCb : 0 < Cb)
    (hd : ∀ u : ℝ, 1 ≤ |u| → ‖Fsum N (2 * N) u‖ ≤
      Cd * (N / |u| + |u| ^ (1 / 2 : ℝ) * Real.log (|u| + 2)))
    (Lf Mf : ℝ → ℕ)
    (hb : ∀ u : ℝ, 10 * N ≤ |u| → ‖Fsum N (2 * N) u‖ ≤ Cb * (N / Real.sqrt |u| *
      ‖Fsum (Lf |u|) (Mf |u|) u‖ + N / Real.sqrt |u| + Real.log (N * |u| + 2)))
    (u : ℝ) (hu1 : u ≠ 0 → 1 ≤ |u|) (huT : |u| ≤ T) :
    ‖Fsum N (2 * N) u‖ ^ 2 ≤ (if u = 0 then ((N : ℝ) + 1) ^ 2 else 0) +
      (2 * Cd ^ 2 * N ^ 2) * (1 / u ^ 2) + 2 * Cd ^ 2 * (10 * N * Real.log (10 * N + 2) ^ 2) +
      (3 * Cb ^ 2 * N) * (if (10 * N : ℝ) < |u| then
        N / |u| * ‖Fsum (Lf |u|) (Mf |u|) u‖ ^ 2 else 0) +
      3 * Cb ^ 2 * (N / 10 + Real.log (N * T + 2) ^ 2) := by
  have hN0 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hT0 : 0 ≤ T := le_trans (abs_nonneg u) huT
  have hL1 : 0 ≤ Real.log (10 * N + 2) := Real.log_nonneg (by linarith)
  have hL2 : 0 ≤ Real.log (N * T + 2) := Real.log_nonneg (by nlinarith)
  have hif : 0 ≤ (if (10 * N : ℝ) < |u| then N / |u| * ‖Fsum (Lf |u|) (Mf |u|) u‖ ^ 2 else 0) := by
    split_ifs <;> positivity
  have hinv : 0 ≤ 1 / u ^ 2 := by positivity
  have hrest : 0 ≤ 2 * Cd ^ 2 * (10 * N * Real.log (10 * N + 2) ^ 2) := by positivity
  have hrest2 : 0 ≤ 3 * Cb ^ 2 * (N / 10 + Real.log (N * T + 2) ^ 2) := by positivity
  have hif0 : 0 ≤ (3 * Cb ^ 2 * N) * (if (10 * N : ℝ) < |u| then
      N / |u| * ‖Fsum (Lf |u|) (Mf |u|) u‖ ^ 2 else 0) := by positivity
  have hinv0 : 0 ≤ (2 * Cd ^ 2 * N ^ 2) * (1 / u ^ 2) := by positivity
  by_cases hu0 : u = 0
  · subst hu0
    rw [if_pos rfl, Fsum_zero]
    have : ‖(N : ℂ) + 1‖ = (N : ℝ) + 1 := by
      rw [show (N : ℂ) + 1 = ((N + 1 : ℕ) : ℂ) by push_cast; ring, Complex.norm_natCast]; push_cast; ring
    rw [this]
    linarith
  rw [if_neg hu0]
  have hu1' := hu1 hu0
  have hupos : 0 < |u| := by linarith
  by_cases hbig : (10 * N : ℝ) < |u|
  · rw [if_pos hbig]
    have h := hb u hbig.le
    set F := ‖Fsum (Lf |u|) (Mf |u|) u‖
    have hs : 0 < Real.sqrt |u| := Real.sqrt_pos.mpr hupos
    have hss : Real.sqrt |u| ^ 2 = |u| := Real.sq_sqrt hupos.le
    set p := N / Real.sqrt |u| * F
    set q := (N : ℝ) / Real.sqrt |u|
    set r := Real.log (N * |u| + 2)
    have hr0 : 0 ≤ r := Real.log_nonneg (by nlinarith)
    have hrT : r ≤ Real.log (N * T + 2) :=
      Real.log_le_log (by nlinarith) (by nlinarith)
    have hp2 : p ^ 2 = N * (N / |u| * F ^ 2) := by
      simp only [p]; rw [div_mul_eq_mul_div, div_pow, hss]; ring
    have hq2 : q ^ 2 ≤ N / 10 := by
      simp only [q]; rw [div_pow, hss, div_le_div_iff₀ hupos (by norm_num)]; nlinarith
    have hp0 : 0 ≤ p := by positivity
    have hq0 : 0 ≤ q := by positivity
    have hE := norm_nonneg (Fsum N (2 * N) u)
    have hsq : ‖Fsum N (2 * N) u‖ ^ 2 ≤ (Cb * (p + q + r)) ^ 2 := pow_le_pow_left₀ hE h 2
    have h3 : (Cb * (p + q + r)) ^ 2 ≤ 3 * Cb ^ 2 * (p ^ 2 + q ^ 2 + r ^ 2) := by
      nlinarith [sq_nonneg (p - q), sq_nonneg (q - r), sq_nonneg (p - r)]
    have hr2 : r ^ 2 ≤ Real.log (N * T + 2) ^ 2 := pow_le_pow_left₀ hr0 hrT 2
    have hCb2 : 0 ≤ 3 * Cb ^ 2 := by positivity
    have : 3 * Cb ^ 2 * (p ^ 2 + q ^ 2 + r ^ 2) ≤ 3 * Cb ^ 2 * N * (N / |u| * F ^ 2) +
        3 * Cb ^ 2 * (N / 10 + Real.log (N * T + 2) ^ 2) := by
      rw [hp2]
      calc 3 * Cb ^ 2 * (N * (N / |u| * F ^ 2) + q ^ 2 + r ^ 2)
          ≤ 3 * Cb ^ 2 * (N * (N / |u| * F ^ 2) + (N / 10 + Real.log (N * T + 2) ^ 2)) := by
            exact mul_le_mul_of_nonneg_left (by linarith) hCb2
        _ = _ := by ring
    linarith
  · rw [if_neg hbig]
    push Not at hbig
    have h := hd u hu1'
    set a := (N : ℝ) / |u|
    set b := |u| ^ (1 / 2 : ℝ) * Real.log (|u| + 2)
    have ha0 : 0 ≤ a := by positivity
    have hb0 : 0 ≤ b := by
      have := Real.log_nonneg (show (1 : ℝ) ≤ |u| + 2 by linarith); positivity
    have hE := norm_nonneg (Fsum N (2 * N) u)
    have hsq : ‖Fsum N (2 * N) u‖ ^ 2 ≤ (Cd * (a + b)) ^ 2 := pow_le_pow_left₀ hE h 2
    have h2 : (Cd * (a + b)) ^ 2 ≤ 2 * Cd ^ 2 * (a ^ 2 + b ^ 2) := by
      have e : 2 * Cd ^ 2 * (a ^ 2 + b ^ 2) - (Cd * (a + b)) ^ 2 = Cd ^ 2 * (a - b) ^ 2 := by ring
      have := mul_nonneg (sq_nonneg Cd) (sq_nonneg (a - b))
      linarith
    have ha2 : a ^ 2 = N ^ 2 * (1 / u ^ 2) := by
      simp only [a]; rw [div_pow, sq_abs]; ring
    have hb2 : b ^ 2 ≤ 10 * N * Real.log (10 * N + 2) ^ 2 := by
      have e : b ^ 2 = |u| * Real.log (|u| + 2) ^ 2 := by
        simp only [b]
        rw [mul_pow, ← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg u)]
        norm_num
      rw [e]
      have hl0 : 0 ≤ Real.log (|u| + 2) := Real.log_nonneg (by linarith)
      have hl : Real.log (|u| + 2) ≤ Real.log (10 * N + 2) := Real.log_le_log (by linarith) (by linarith)
      have := pow_le_pow_left₀ hl0 hl 2
      exact mul_le_mul hbig this (sq_nonneg _) (by positivity)
    have : 2 * Cd ^ 2 * (a ^ 2 + b ^ 2) ≤ (2 * Cd ^ 2 * N ^ 2) * (1 / u ^ 2) +
        2 * Cd ^ 2 * (10 * N * Real.log (10 * N + 2) ^ 2) := by
      rw [ha2]; have h2c : 0 ≤ 2 * Cd ^ 2 := by positivity
      have := mul_le_mul_of_nonneg_left hb2 h2c
      linarith
    linarith

/-! ## Summing the pointwise bound -/
lemma sum_bound (A : Finset ℝ) (hsep : IsSeparated 1 A) (N : ℕ) (hN : 1 ≤ N) (T Cd Cb : ℝ)
    (hCd : 0 < Cd) (hCb : 0 < Cb)
    (hd : ∀ u : ℝ, 1 ≤ |u| → ‖Fsum N (2 * N) u‖ ≤
      Cd * (N / |u| + |u| ^ (1 / 2 : ℝ) * Real.log (|u| + 2)))
    (Lf Mf : ℝ → ℕ)
    (hb : ∀ u : ℝ, 10 * N ≤ |u| → ‖Fsum N (2 * N) u‖ ≤ Cb * (N / Real.sqrt |u| *
      ‖Fsum (Lf |u|) (Mf |u|) u‖ + N / Real.sqrt |u| + Real.log (N * |u| + 2)))
    (hT : ∀ x ∈ A, ∀ y ∈ A, |x - y| ≤ T) :
    ∑ x ∈ A, ∑ y ∈ A, ‖Fsum N (2 * N) (x - y)‖ ^ 2 ≤
      A.card * ((N : ℝ) + 1) ^ 2 + A.card * ((2 * Cd ^ 2 * N ^ 2) * 4) +
      A.card * (A.card * (2 * Cd ^ 2 * (10 * N * Real.log (10 * N + 2) ^ 2))) +
      (3 * Cb ^ 2 * N) * ∑ x ∈ A, ∑ y ∈ A, (if (10 * N : ℝ) < |x - y| then
        N / |x - y| * ‖Fsum (Lf |x - y|) (Mf |x - y|) (x - y)‖ ^ 2 else 0) +
      A.card * (A.card * (3 * Cb ^ 2 * (N / 10 + Real.log (N * T + 2) ^ 2))) := by
  have hin : ∀ x ∈ A, ∑ y ∈ A, ‖Fsum N (2 * N) (x - y)‖ ^ 2 ≤
      ((N : ℝ) + 1) ^ 2 + (2 * Cd ^ 2 * N ^ 2) * 4 +
      A.card * (2 * Cd ^ 2 * (10 * N * Real.log (10 * N + 2) ^ 2)) +
      (3 * Cb ^ 2 * N) * ∑ y ∈ A, (if (10 * N : ℝ) < |x - y| then
        N / |x - y| * ‖Fsum (Lf |x - y|) (Mf |x - y|) (x - y)‖ ^ 2 else 0) +
      A.card * (3 * Cb ^ 2 * (N / 10 + Real.log (N * T + 2) ^ 2)) := by
    intro x hx
    have h1 : ∑ y ∈ A, (if x - y = 0 then ((N : ℝ) + 1) ^ 2 else 0) = ((N : ℝ) + 1) ^ 2 := by
      simp_rw [sub_eq_zero]; rw [Finset.sum_ite_eq]; simp [hx]
    have h2 : ∑ y ∈ A, 1 / (x - y) ^ 2 ≤ 4 := by
      rw [← Finset.sum_erase A (a := x) (by simp)]
      exact GuthMaynard.CitedLV.PartH.sum_inv_sq_le_of_separated A id
        (fun r hr q hq h => hsep r hr q hq h) x hx
    have h2' := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 2 * Cd ^ 2 * N ^ 2)
    calc ∑ y ∈ A, ‖Fsum N (2 * N) (x - y)‖ ^ 2
        ≤ ∑ y ∈ A, ((if x - y = 0 then ((N : ℝ) + 1) ^ 2 else 0) +
            (2 * Cd ^ 2 * N ^ 2) * (1 / (x - y) ^ 2) +
            2 * Cd ^ 2 * (10 * N * Real.log (10 * N + 2) ^ 2) +
            (3 * Cb ^ 2 * N) * (if (10 * N : ℝ) < |x - y| then
              N / |x - y| * ‖Fsum (Lf |x - y|) (Mf |x - y|) (x - y)‖ ^ 2 else 0) +
            3 * Cb ^ 2 * (N / 10 + Real.log (N * T + 2) ^ 2)) := by
          refine Finset.sum_le_sum fun y hy => ?_
          refine pointwise N hN T Cd Cb hCd hCb hd Lf Mf hb (x - y) (fun h => ?_) (hT x hx y hy)
          exact hsep x hx y hy (fun e => h (by rw [e, sub_self]))
      _ = (∑ y ∈ A, (if x - y = 0 then ((N : ℝ) + 1) ^ 2 else 0)) +
            (2 * Cd ^ 2 * N ^ 2) * ∑ y ∈ A, 1 / (x - y) ^ 2 +
            A.card * (2 * Cd ^ 2 * (10 * N * Real.log (10 * N + 2) ^ 2)) +
            (3 * Cb ^ 2 * N) * ∑ y ∈ A, (if (10 * N : ℝ) < |x - y| then
              N / |x - y| * ‖Fsum (Lf |x - y|) (Mf |x - y|) (x - y)‖ ^ 2 else 0) +
            A.card * (3 * Cb ^ 2 * (N / 10 + Real.log (N * T + 2) ^ 2)) := by
          simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
          ring
      _ ≤ _ := by rw [h1]; linarith
  calc ∑ x ∈ A, ∑ y ∈ A, ‖Fsum N (2 * N) (x - y)‖ ^ 2
      ≤ ∑ x ∈ A, (((N : ℝ) + 1) ^ 2 + (2 * Cd ^ 2 * N ^ 2) * 4 +
      A.card * (2 * Cd ^ 2 * (10 * N * Real.log (10 * N + 2) ^ 2)) +
      (3 * Cb ^ 2 * N) * ∑ y ∈ A, (if (10 * N : ℝ) < |x - y| then
        N / |x - y| * ‖Fsum (Lf |x - y|) (Mf |x - y|) (x - y)‖ ^ 2 else 0) +
      A.card * (3 * Cb ^ 2 * (N / 10 + Real.log (N * T + 2) ^ 2))) := Finset.sum_le_sum hin
    _ = _ := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
      ring

/-! ## Dyadic shells -/
lemma exists_shell (N : ℕ) (hN : 1 ≤ N) (T v : ℝ) (hv : 10 * (N : ℝ) < v) (hvT : v ≤ T) :
    ∃ j ∈ Finset.range (Nat.log 2 ⌈T⌉₊ + 1),
      10 * (N : ℝ) * 2 ^ j < v ∧ v ≤ 2 * (10 * (N : ℝ) * 2 ^ j) := by
  have hN0 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hex : ∃ k : ℕ, v ≤ 10 * (N : ℝ) * 2 ^ k := by
    obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt v (by norm_num : (1 : ℝ) < 2)
    refine ⟨k, ?_⟩
    have : (0 : ℝ) ≤ 2 ^ k := by positivity
    nlinarith
  classical
  have hk := Nat.find_spec hex
  have hk0 : Nat.find hex ≠ 0 := by
    intro h; rw [h] at hk; simp at hk; linarith
  obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hk0
  have hjmin : ¬ v ≤ 10 * (N : ℝ) * 2 ^ j := Nat.find_min hex (by omega)
  push Not at hjmin
  refine ⟨j, ?_, hjmin, ?_⟩
  · rw [Finset.mem_range, Nat.lt_succ_iff]
    apply Nat.le_log_of_pow_le (by norm_num)
    have h1 : (2 : ℝ) ^ j ≤ ⌈T⌉₊ := by
      have : (2 : ℝ) ^ j ≤ 10 * N * 2 ^ j := by
        have : (0 : ℝ) ≤ 2 ^ j := by positivity
        nlinarith
      linarith [Nat.le_ceil T]
    exact_mod_cast h1
  · rw [hj, pow_succ] at hk; linarith

lemma cover (A : Finset ℝ) (T : ℝ) (N : ℕ) (hN : 1 ≤ N) (hT : ∀ x ∈ A, ∀ y ∈ A, |x - y| ≤ T)
    (g : ℝ → ℝ → ℝ) (hg : ∀ x ∈ A, ∀ y ∈ A, 0 ≤ g x y) :
    ∑ x ∈ A, ∑ y ∈ A, (if 10 * (N : ℝ) < |x - y| then g x y else 0) ≤
      ∑ j ∈ range (Nat.log 2 ⌈T⌉₊ + 1), ∑ x ∈ A, ∑ y ∈ A,
        (if 10 * (N : ℝ) * 2 ^ j < |x - y| ∧ |x - y| ≤ 2 * (10 * (N : ℝ) * 2 ^ j)
          then g x y else 0) := by
  have e : ∑ j ∈ range (Nat.log 2 ⌈T⌉₊ + 1), ∑ x ∈ A, ∑ y ∈ A,
        (if 10 * (N : ℝ) * 2 ^ j < |x - y| ∧ |x - y| ≤ 2 * (10 * (N : ℝ) * 2 ^ j)
          then g x y else 0) =
      ∑ x ∈ A, ∑ y ∈ A, ∑ j ∈ range (Nat.log 2 ⌈T⌉₊ + 1),
        (if 10 * (N : ℝ) * 2 ^ j < |x - y| ∧ |x - y| ≤ 2 * (10 * (N : ℝ) * 2 ^ j)
          then g x y else 0) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun x _ => Finset.sum_comm
  rw [e]
  refine Finset.sum_le_sum fun x hx => Finset.sum_le_sum fun y hy => ?_
  have hnn : ∀ j ∈ range (Nat.log 2 ⌈T⌉₊ + 1), (0 : ℝ) ≤
      (if 10 * (N : ℝ) * 2 ^ j < |x - y| ∧ |x - y| ≤ 2 * (10 * (N : ℝ) * 2 ^ j)
        then g x y else 0) := fun j _ => by
    split_ifs
    · exact hg x hx y hy
    · exact le_rfl
  split_ifs with h
  · obtain ⟨j, hj, hs⟩ := exists_shell N hN T |x - y| h (hT x hx y hy)
    calc g x y = (if 10 * (N : ℝ) * 2 ^ j < |x - y| ∧ |x - y| ≤ 2 * (10 * (N : ℝ) * 2 ^ j)
          then g x y else 0) := (if_pos hs).symm
      _ ≤ _ := Finset.single_le_sum hnn hj
  · exact Finset.sum_nonneg hnn

/-! ## Step 1: unit coefficients -/
lemma step1 (A : Finset ℝ) (N : ℕ) (hN : 1 ≤ N) :
    S A N ≤ (1 / N) * ∑ x ∈ A, ∑ y ∈ A, ‖Fsum N (2 * N) (x - y)‖ ^ 2 := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  set c : ℝ := (N : ℝ) ^ (-(1 / 2 : ℝ)) with hcdef
  have h := majorant A N (2 * N) hN w (fun _ => c) (fun n hn => by
    rw [Finset.mem_Icc] at hn
    have hn' : (N : ℝ) ≤ n := by exact_mod_cast hn.1
    unfold w
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)]
    exact Real.rpow_le_rpow_of_nonpos hN0 hn' (by norm_num))
  have e : (fun _ : ℕ => ((c : ℝ) : ℂ)) = fun n => (c : ℂ) * (fun _ : ℕ => (1 : ℂ)) n := by
    funext n; simp
  rw [e, Q_const_mul] at h
  have hc : ‖(c : ℂ)‖ ^ 2 = 1 / N := by
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, hcdef, ← Real.rpow_natCast,
      ← Real.rpow_mul hN0.le]
    norm_num
    rw [Real.rpow_neg_one]
  have hQ : Q A (D (fun _ => (1 : ℂ)) N (2 * N)) =
      ∑ x ∈ A, ∑ y ∈ A, ‖Fsum N (2 * N) (x - y)‖ ^ 2 := by
    unfold Q D Fsum; simp only [one_mul]
  rw [hc, hQ] at h
  exact h

/-! ## One shell -/
lemma shell_bound (A : Finset ℝ) (T : ℝ) (N M : ℕ) (Cc Cm ε' : ℝ) (hCc : 0 < Cc) (hCm : 0 < Cm)
    (hcomp : ∀ (A : Finset ℝ) (L U : ℕ), 1 ≤ L → ∀ (a : ℕ → ℂ)
      (lo hi : ℝ → ℝ → ℕ), (∀ x ∈ A, ∀ y ∈ A, L ≤ lo x y ∧ hi x y ≤ U) →
      ∑ x ∈ A, ∑ y ∈ A, ‖∑ n ∈ Finset.Icc (lo x y) (hi x y), a n * (n : ℂ) ^ (((x - y : ℝ) : ℂ) * I)‖ ^ 2
        ≤ Cc * (1 + Real.log (U + 1)) ^ 2 * Q A (D (fun n => ((‖a n‖ : ℝ) : ℂ)) L U))
    (hmono : ∀ (A : Finset ℝ) (N M : ℕ), 1 ≤ N → 64 * N ≤ M → S A N ≤ Cm * (M : ℝ) ^ ε' * S A M)
    (hT : ∀ x ∈ A, ∀ y ∈ A, |x - y| ≤ T) (hN : 1 ≤ N) (hM : 64 * (T / N + 1) ≤ M)
    (Lf Mf : ℝ → ℕ) (hLf : ∀ t : ℝ, 10 * N ≤ t →
      t / (8 * Real.pi * N) ≤ Lf t ∧ (Mf t : ℝ) ≤ t / (Real.pi * N) + 1)
    (j : ℕ) :
    ∑ x ∈ A, ∑ y ∈ A, (if 10 * (N : ℝ) * 2 ^ j < |x - y| ∧ |x - y| ≤ 2 * (10 * (N : ℝ) * 2 ^ j)
        then N / |x - y| * ‖Fsum (Lf |x - y|) (Mf |x - y|) (x - y)‖ ^ 2 else 0)
      ≤ Cc * (1 + Real.log (M + 1)) ^ 2 *
        (4 ^ 5 * (Cc * (1 + Real.log (M + 1)) ^ 2 * (Cm * (M : ℝ) ^ ε' * S A M))) := by
  set G := Cc * (1 + Real.log (M + 1)) ^ 2 * (Cm * (M : ℝ) ^ ε' * S A M) with hGdef
  have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  have hlM : 0 ≤ 1 + Real.log (M + 1) := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ M + 1 by linarith); linarith
  have hG : 0 ≤ G := by have := S_nonneg A M; positivity
  have hN0 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  have hRHS : 0 ≤ Cc * (1 + Real.log (M + 1)) ^ 2 * (4 ^ 5 * G) := by positivity
  have h2j : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
  set Δ : ℝ := 10 * (N : ℝ) * 2 ^ j with hΔ
  have hΔ10 : 10 * (N : ℝ) ≤ Δ := by nlinarith
  have hΔpos : 0 < Δ := by linarith
  by_cases hΔT : T ≤ Δ
  · calc _ = (0 : ℝ) := Finset.sum_eq_zero fun x hx => Finset.sum_eq_zero fun y hy =>
          if_neg (by have := hT x hx y hy; intro h; linarith [h.1])
      _ ≤ _ := hRHS
  push Not at hΔT
  have hpi3 : 3 < Real.pi := Real.pi_gt_three
  have hpi4 : Real.pi < 4 := Real.pi_lt_four
  have hpiN : 0 < Real.pi * N := by positivity
  have h8piN : 0 < 8 * Real.pi * N := by positivity
  set lam : ℝ := Δ / (8 * Real.pi * N) with hlam
  set mu : ℝ := 2 * Δ / (Real.pi * N) + 1 with hmu
  have hlam16 : 1 / 16 < lam := by
    rw [hlam, lt_div_iff₀ h8piN]; nlinarith
  have hmu_eq : mu = 16 * lam + 1 := by
    rw [hmu, hlam]; field_simp; ring
  have hmu32 : mu < 32 * lam := by linarith
  have hmuT : mu ≤ T / N + 1 := by
    rw [hmu]
    have : 2 * Δ / (Real.pi * N) ≤ T / N := by
      rw [div_le_div_iff₀ hpiN hNpos]
      have h1 : 0 < (N : ℝ) * (T - Δ) := mul_pos hNpos (by linarith)
      have h2 : 0 ≤ (N : ℝ) * T * (Real.pi - 3) := mul_nonneg (mul_nonneg hNpos.le (by linarith)) (by linarith)
      have h3 : 0 ≤ (N : ℝ) * T := mul_nonneg hNpos.le (by linarith)
      nlinarith
    linarith
  set L0 := ⌈lam⌉₊ with hL0def
  set U0 := ⌊mu⌋₊ with hU0def
  have hL0 : 1 ≤ L0 := Nat.one_le_iff_ne_zero.mpr (Nat.pos_iff_ne_zero.mp (Nat.ceil_pos.mpr (by linarith)))
  have hmu0 : 0 ≤ mu := by linarith
  have hU0mu : (U0 : ℝ) ≤ mu := Nat.floor_le hmu0
  have hU0L0 : U0 < L0 * 2 ^ 5 := by
    have : (U0 : ℝ) < (L0 : ℝ) * 2 ^ 5 := by
      have := Nat.le_ceil lam; norm_num; linarith
    exact_mod_cast this
  have hU0M : 64 * U0 ≤ M := by
    have : (64 * U0 : ℝ) ≤ M := by linarith
    exact_mod_cast this
  -- the ranges for `completion`
  let lo : ℝ → ℝ → ℕ := fun x y =>
    if Δ < |x - y| ∧ |x - y| ≤ 2 * Δ then Lf |x - y| else L0
  let hi : ℝ → ℝ → ℕ := fun x y =>
    if Δ < |x - y| ∧ |x - y| ≤ 2 * Δ then Mf |x - y| else 0
  have hrange : ∀ x ∈ A, ∀ y ∈ A, L0 ≤ lo x y ∧ hi x y ≤ U0 := by
    intro x _ y _
    by_cases hs : Δ < |x - y| ∧ |x - y| ≤ 2 * Δ
    · simp only [lo, hi, if_pos hs]
      obtain ⟨hl, hm⟩ := hLf |x - y| (by linarith [hs.1])
      constructor
      · apply Nat.ceil_le.mpr
        refine le_trans ?_ hl
        exact div_le_div_of_nonneg_right hs.1.le h8piN.le
      · apply Nat.le_floor
        refine le_trans hm ?_
        have : |x - y| / (Real.pi * N) ≤ 2 * Δ / (Real.pi * N) :=
          div_le_div_of_nonneg_right hs.2 hpiN.le
        linarith
    · simp only [lo, hi, if_neg hs]
      exact ⟨le_rfl, Nat.zero_le _⟩
  have hA := hcomp A L0 U0 hL0 (fun _ => (1 : ℂ)) lo hi hrange
  -- Step A
  have hstepA : ∑ x ∈ A, ∑ y ∈ A, (if Δ < |x - y| ∧ |x - y| ≤ 2 * Δ
        then N / |x - y| * ‖Fsum (Lf |x - y|) (Mf |x - y|) (x - y)‖ ^ 2 else 0) ≤
      N / Δ * ∑ x ∈ A, ∑ y ∈ A, ‖∑ n ∈ Finset.Icc (lo x y) (hi x y),
        (fun _ => (1 : ℂ)) n * (n : ℂ) ^ (((x - y : ℝ) : ℂ) * I)‖ ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun x _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun y _ => ?_
    by_cases hs : Δ < |x - y| ∧ |x - y| ≤ 2 * Δ
    · simp only [lo, hi, if_pos hs, one_mul]
      unfold Fsum
      gcongr
      exact hs.1.le
    · rw [if_neg hs]; positivity
  -- Step C: majorant
  have hstepC : Q A (D (fun n => ((‖(fun _ => (1 : ℂ)) n‖ : ℝ) : ℂ)) L0 U0) ≤
      mu * Q A (D w L0 U0) := by
    have h := majorant A L0 U0 hL0 (fun n => ((‖(fun _ => (1 : ℂ)) n‖ : ℝ) : ℂ))
      (fun n => Real.sqrt mu * (n : ℝ) ^ (-(1 / 2 : ℝ))) (fun n hn => by
        rw [Finset.mem_Icc] at hn
        have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast le_trans hL0 hn.1
        have hnmu : (n : ℝ) ≤ mu := le_trans (by exact_mod_cast hn.2) hU0mu
        simp only [norm_one, Complex.ofReal_one]
        rw [Real.rpow_neg (by linarith), ← Real.sqrt_eq_rpow, ← div_eq_mul_inv,
          one_le_div (Real.sqrt_pos.mpr (by linarith))]
        exact Real.sqrt_le_sqrt hnmu)
    have e : (fun n : ℕ => (((Real.sqrt mu * (n : ℝ) ^ (-(1 / 2 : ℝ))) : ℝ) : ℂ)) =
        fun n => (Real.sqrt mu : ℂ) * w n := by
      funext n; unfold w; push_cast; ring
    rw [e, Q_const_mul, Complex.norm_real, Real.norm_eq_abs, sq_abs, Real.sq_sqrt hmu0] at h
    exact h
  -- Step D: dyadic pieces
  have hstepD : Q A (D w L0 U0) ≤ 4 ^ 5 * G :=
    range_bound A M G hG (fun K hi hK hKM hhi =>
      piece_bound A M ε' Cc Cm hCc hcomp hmono K hi hK hKM hhi) 5 L0 U0 hL0 hU0L0 hU0M
  -- combine
  have hlU : 0 ≤ 1 + Real.log ((U0 : ℝ) + 1) := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ U0 + 1 by have := Nat.cast_nonneg (α := ℝ) U0; linarith)
    linarith
  have hlUM : (1 + Real.log ((U0 : ℝ) + 1)) ^ 2 ≤ (1 + Real.log (M + 1)) ^ 2 := by
    gcongr
    have : U0 ≤ M := by omega
    exact_mod_cast this
  have hNmu : N / Δ * mu ≤ 1 := by
    rw [hmu, div_mul_eq_mul_div, div_le_one hΔpos]
    have : (N : ℝ) * (2 * Δ / (Real.pi * N)) = 2 * Δ / Real.pi := by field_simp
    rw [mul_add, this, mul_one]
    have : 2 * Δ / Real.pi ≤ 2 * Δ / 3 := div_le_div_of_nonneg_left (by linarith) (by norm_num) hpi3.le
    linarith
  have hQw : 0 ≤ Q A (D w L0 U0) := Q_nonneg _ _
  have hNΔ : 0 ≤ N / Δ := by positivity
  calc _ ≤ N / Δ * ∑ x ∈ A, ∑ y ∈ A, ‖∑ n ∈ Finset.Icc (lo x y) (hi x y),
        (fun _ => (1 : ℂ)) n * (n : ℂ) ^ (((x - y : ℝ) : ℂ) * I)‖ ^ 2 := hstepA
    _ ≤ N / Δ * (Cc * (1 + Real.log ((U0 : ℝ) + 1)) ^ 2 * (mu * Q A (D w L0 U0))) := by
        gcongr; exact le_trans hA (by gcongr)
    _ = Cc * (1 + Real.log ((U0 : ℝ) + 1)) ^ 2 * ((N / Δ * mu) * Q A (D w L0 U0)) := by ring
    _ ≤ Cc * (1 + Real.log (M + 1)) ^ 2 * (1 * (4 ^ 5 * G)) := by
        gcongr
    _ = _ := by ring

/-! ## Logarithms -/
lemma log_pow_five_le (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 1 ≤ T → (1 + Real.log T) ^ 5 ≤ C * T ^ ε := by
  set δ := ε / 5 with hδ
  have hδ0 : 0 < δ := by positivity
  refine ⟨(1 + 1 / δ) ^ 5, by positivity, fun T hT => ?_⟩
  have h1 : Real.log T ≤ T ^ δ / δ := Real.log_le_rpow_div (by linarith) hδ0
  have h2 : 1 ≤ T ^ δ := Real.one_le_rpow hT hδ0.le
  have h3 : 1 + Real.log T ≤ (1 + 1 / δ) * T ^ δ := by
    have : T ^ δ / δ = (1 / δ) * T ^ δ := by ring
    rw [this] at h1
    nlinarith
  have h0 : 0 ≤ 1 + Real.log T := by have := Real.log_nonneg hT; linarith
  calc (1 + Real.log T) ^ 5 ≤ ((1 + 1 / δ) * T ^ δ) ^ 5 := pow_le_pow_left₀ h0 h3 5
    _ = (1 + 1 / δ) ^ 5 * T ^ ε := by
      rw [mul_pow, ← Real.rpow_mul_natCast (by linarith)]
      congr 2; rw [hδ]; push_cast; ring

lemma log_bounds (T : ℝ) (hT : 2 ≤ T) (N M : ℕ) (hN : 1 ≤ N) (hNT : (N : ℝ) ≤ T)
    (hM : (M : ℝ) ≤ 200 * T ^ 2) :
    Real.log (10 * N + 2) ≤ 11 * (1 + Real.log T) ∧
    Real.log (N * T + 2) ≤ 2 * (1 + Real.log T) ∧
    1 + Real.log (M + 1) ≤ 201 * (1 + Real.log T) ∧
    ((Nat.log 2 ⌈T⌉₊ + 1 : ℕ) : ℝ) ≤ 3 * (1 + Real.log T) := by
  have hN0 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hT0 : 0 < T := by linarith
  have hlT : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
  have hlog_le (c : ℝ) (hc : 0 < c) : Real.log c ≤ c - 1 := Real.log_le_sub_one_of_pos hc
  refine ⟨?_, ?_, ?_, ?_⟩
  · calc Real.log (10 * N + 2) ≤ Real.log (12 * T) := Real.log_le_log (by positivity) (by linarith)
      _ = Real.log 12 + Real.log T := Real.log_mul (by norm_num) hT0.ne'
      _ ≤ 11 * (1 + Real.log T) := by have := hlog_le 12 (by norm_num); linarith
  · calc Real.log (N * T + 2) ≤ Real.log (2 * T ^ 2) :=
          Real.log_le_log (by positivity) (by nlinarith)
      _ = Real.log 2 + 2 * Real.log T := by
          rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]; push_cast; ring
      _ ≤ 2 * (1 + Real.log T) := by have := hlog_le 2 (by norm_num); linarith
  · have : Real.log (M + 1) ≤ 200 + 2 * Real.log T := by
      calc Real.log (M + 1) ≤ Real.log (201 * T ^ 2) :=
            Real.log_le_log (by positivity) (by nlinarith)
        _ = Real.log 201 + 2 * Real.log T := by
            rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]; push_cast; ring
        _ ≤ 200 + 2 * Real.log T := by have := hlog_le 201 (by norm_num); linarith
    linarith
  · set n := ⌈T⌉₊ with hn
    have hn1 : (n : ℝ) < T + 1 := Nat.ceil_lt_add_one hT0.le
    have hnT : T ≤ n := Nat.le_ceil T
    have hn0 : n ≠ 0 := by
      intro h; rw [h] at hnT; simp at hnT; linarith
    have hpow := Nat.pow_log_le_self 2 hn0
    set k := Nat.log 2 n
    have hpowR : (2 : ℝ) ^ k ≤ n := by exact_mod_cast hpow
    have hlk : (k : ℝ) * Real.log 2 ≤ Real.log n := by
      rw [← Real.log_pow]; exact Real.log_le_log (by positivity) hpowR
    have hln : Real.log n ≤ Real.log 2 + Real.log T := by
      rw [← Real.log_mul (by norm_num) hT0.ne']
      exact Real.log_le_log (by positivity) (by linarith)
    have hl2 := Real.log_two_gt_d9
    have hl2' : Real.log 2 ≤ 1 := by have := hlog_le 2 (by norm_num); linarith
    have hk : (k : ℝ) ≤ 1 + 2 * Real.log T := by
      have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      by_contra hcon
      push Not at hcon
      have : (1 + 2 * Real.log T) * Real.log 2 < (k : ℝ) * Real.log 2 :=
        mul_lt_mul_of_pos_right hcon (by linarith)
      nlinarith
    push_cast
    linarith

/-! ## Final arithmetic -/
lemma final_arith (N R T ε Cd Cb Cl c X Sfar SN L1 L2 : ℝ) (hε : 0 < ε) (hN0 : 1 ≤ N)
    (hR0 : 0 ≤ R) (hT1 : 1 ≤ T) (hX0 : 0 ≤ X) (hCd : 0 < Cd) (hCb : 0 < Cb) (hCl : 0 < Cl)
    (hc0 : 0 < c) (hL1 : L1 ≤ 11 * (1 + Real.log T)) (hL2 : L2 ≤ 2 * (1 + Real.log T))
    (hL1' : 0 ≤ L1) (hL2'' : 0 ≤ L2)
    (hℓ5 : (1 + Real.log T) ^ 5 ≤ Cl * T ^ (ε / 2))
    (hs : SN ≤ (1 / N) * (R * (N + 1) ^ 2 + R * ((2 * Cd ^ 2 * N ^ 2) * 4) +
      R * (R * (2 * Cd ^ 2 * (10 * N * L1 ^ 2))) + (3 * Cb ^ 2 * N) * Sfar +
      R * (R * (3 * Cb ^ 2 * (N / 10 + L2 ^ 2)))))
    (hfar : 3 * Cb ^ 2 * Sfar ≤ c * (1 + Real.log T) ^ 5 * T ^ (ε / 2) * X) :
    SN ≤ ((4 + 8 * Cd ^ 2) + (20 * Cd ^ 2 * 121 + 3 * Cb ^ 2 * (1 / 10 + 4)) * Cl + c * Cl) *
      T ^ ε * (X + R ^ 2 + N * R) := by
  set a : ℝ := 4 + 8 * Cd ^ 2 with ha
  set b : ℝ := 20 * Cd ^ 2 * 121 + 3 * Cb ^ 2 * (1 / 10 + 4) with hb
  have ha0 : 0 < a := by positivity
  have hb0 : 0 < b := by positivity
  set ℓ := 1 + Real.log T with hℓ
  have hℓ1 : 1 ≤ ℓ := by have := Real.log_nonneg hT1; linarith
  have hNpos : (0 : ℝ) < N := by linarith
  have t1 : (1 / (N : ℝ)) * (R * ((N : ℝ) + 1) ^ 2) ≤ 4 * (N * R) := by
    have e : (1 / (N : ℝ)) * (R * ((N : ℝ) + 1) ^ 2) = R * (((N : ℝ) + 1) ^ 2 / N) := by ring
    have h : ((N : ℝ) + 1) ^ 2 / N ≤ 4 * N := by
      rw [div_le_iff₀ hNpos]; nlinarith
    rw [e]; nlinarith
  have t2 : (1 / (N : ℝ)) * (R * ((2 * Cd ^ 2 * N ^ 2) * 4)) = 8 * Cd ^ 2 * (N * R) := by
    field_simp; ring
  have t3 : (1 / (N : ℝ)) * (R * (R * (2 * Cd ^ 2 * (10 * N * L1 ^ 2)))) ≤
      20 * Cd ^ 2 * 121 * ℓ ^ 2 * R ^ 2 := by
    have e : (1 / (N : ℝ)) * (R * (R * (2 * Cd ^ 2 * (10 * N * L1 ^ 2)))) =
        20 * Cd ^ 2 * L1 ^ 2 * R ^ 2 := by field_simp; ring
    have h : L1 ^ 2 ≤ 121 * ℓ ^ 2 := by
      calc L1 ^ 2 ≤ (11 * ℓ) ^ 2 := pow_le_pow_left₀ hL1' hL1 2
        _ = 121 * ℓ ^ 2 := by ring
    rw [e]
    have : 0 ≤ 20 * Cd ^ 2 * R ^ 2 := by positivity
    nlinarith
  have t4 : (1 / (N : ℝ)) * ((3 * Cb ^ 2 * N) * Sfar) = 3 * Cb ^ 2 * Sfar := by
    field_simp
  have t5 : (1 / (N : ℝ)) * (R * (R * (3 * Cb ^ 2 * (N / 10 + L2 ^ 2)))) ≤
      3 * Cb ^ 2 * (1 / 10 + 4) * ℓ ^ 2 * R ^ 2 := by
    have e : (1 / (N : ℝ)) * (R * (R * (3 * Cb ^ 2 * (N / 10 + L2 ^ 2)))) =
        3 * Cb ^ 2 * R ^ 2 * (1 / 10 + L2 ^ 2 / N) := by field_simp
    have h1 : L2 ^ 2 / N ≤ L2 ^ 2 :=
      div_le_self (sq_nonneg _) hN0
    have h2 : L2 ^ 2 ≤ 4 * ℓ ^ 2 := by
      calc L2 ^ 2 ≤ (2 * ℓ) ^ 2 := pow_le_pow_left₀ hL2'' hL2 2
        _ = 4 * ℓ ^ 2 := by ring
    have h3 : (1 : ℝ) ≤ ℓ ^ 2 := one_le_pow₀ hℓ1
    rw [e]
    have : 0 ≤ 3 * Cb ^ 2 * R ^ 2 := by positivity
    have : 1 / 10 + L2 ^ 2 / N ≤ (1 / 10 + 4) * ℓ ^ 2 := by linarith
    calc 3 * Cb ^ 2 * R ^ 2 * (1 / 10 + L2 ^ 2 / N)
        ≤ 3 * Cb ^ 2 * R ^ 2 * ((1 / 10 + 4) * ℓ ^ 2) := by gcongr
      _ = _ := by ring
  have core : SN ≤ a * (N * R) + b * ℓ ^ 2 * R ^ 2 + c * ℓ ^ 5 * T ^ (ε / 2) * X := by
    have h := hs
    rw [mul_add, mul_add, mul_add, mul_add] at h
    rw [t2, t4] at h
    calc SN ≤ 4 * (N * R) + 8 * Cd ^ 2 * (N * R) + 20 * Cd ^ 2 * 121 * ℓ ^ 2 * R ^ 2 +
          c * ℓ ^ 5 * T ^ (ε / 2) * X + 3 * Cb ^ 2 * (1 / 10 + 4) * ℓ ^ 2 * R ^ 2 := by
          linarith
      _ = a * (N * R) + b * ℓ ^ 2 * R ^ 2 + c * ℓ ^ 5 * T ^ (ε / 2) * X := by
          rw [ha, hb]; ring
  -- absorb the logarithms
  have hTε : 1 ≤ T ^ ε := Real.one_le_rpow hT1 hε.le
  have hTh : T ^ (ε / 2) ≤ T ^ ε := Real.rpow_le_rpow_of_exponent_le hT1 (by linarith)
  have hTh0 : 0 ≤ T ^ (ε / 2) := by positivity
  have hℓ2 : ℓ ^ 2 ≤ Cl * T ^ ε := by
    have : ℓ ^ 2 ≤ ℓ ^ 5 := pow_le_pow_right₀ hℓ1 (by norm_num)
    have : Cl * T ^ (ε / 2) ≤ Cl * T ^ ε := mul_le_mul_of_nonneg_left hTh hCl.le
    linarith
  have hℓ5' : ℓ ^ 5 * T ^ (ε / 2) ≤ Cl * T ^ ε := by
    calc ℓ ^ 5 * T ^ (ε / 2) ≤ Cl * T ^ (ε / 2) * T ^ (ε / 2) := by gcongr
      _ = Cl * T ^ ε := by rw [mul_assoc, ← Real.rpow_add (by linarith)]; ring_nf
  have e1 : a * (N * R) ≤ a * T ^ ε * (N * R) :=
    mul_le_mul_of_nonneg_right (le_mul_of_one_le_right ha0.le hTε) (by positivity)
  have e2 : b * ℓ ^ 2 * R ^ 2 ≤ b * Cl * T ^ ε * R ^ 2 := by
    have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hℓ2 hb0.le) (sq_nonneg R)
    exact le_of_le_of_eq this (by ring)
  have e3 : c * ℓ ^ 5 * T ^ (ε / 2) * X ≤ c * Cl * T ^ ε * X := by
    have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hℓ5' hc0.le) hX0
    calc c * ℓ ^ 5 * T ^ (ε / 2) * X = c * (ℓ ^ 5 * T ^ (ε / 2)) * X := by ring
      _ ≤ c * (Cl * T ^ ε) * X := this
      _ = _ := by ring
  have hTε0 : 0 ≤ T ^ ε := by positivity
  have p1 : 0 ≤ a * T ^ ε * X := by positivity
  have p2 : 0 ≤ a * T ^ ε * R ^ 2 := by positivity
  have p3 : 0 ≤ b * Cl * T ^ ε * X := by positivity
  have p4 : 0 ≤ b * Cl * T ^ ε * (N * R) := by positivity
  have p5 : 0 ≤ c * Cl * T ^ ε * R ^ 2 := by positivity
  have p6 : 0 ≤ c * Cl * T ^ ε * (N * R) := by positivity
  have fin : (a + b * Cl + c * Cl) * T ^ ε * (X + R ^ 2 + N * R) =
      a * T ^ ε * (N * R) + b * Cl * T ^ ε * R ^ 2 + c * Cl * T ^ ε * X +
      (a * T ^ ε * X + a * T ^ ε * R ^ 2 + b * Cl * T ^ ε * X +
        b * Cl * T ^ ε * (N * R) + c * Cl * T ^ ε * R ^ 2 + c * Cl * T ^ ε * (N * R)) := by ring
  rw [fin]
  linarith

/-! ## The target -/
theorem dual : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ (A : Finset ℝ) (T : ℝ) (N M : ℕ),
    IsSeparated 1 A → (∀ x ∈ A, ∀ y ∈ A, |x - y| ≤ T) → 2 ≤ T → 1 ≤ N → (N : ℝ) ≤ T →
    64 * (T / N + 1) ≤ M → (M : ℝ) ≤ 200 * T ^ 2 →
    S A N ≤ C * T ^ ε * (S A M + (A.card : ℝ) ^ 2 + N * A.card) := by
  intro ε hε
  obtain ⟨Cm, hCm, hmono⟩ := GuthMaynard.CitedLV.HB.mono (ε / 4) (by positivity)
  obtain ⟨Cc, hCc, hcomp⟩ := GuthMaynard.CitedLV.HB.completion
  obtain ⟨Cd, hCd, hdy⟩ := GuthMaynard.CitedLV.HB.dyadic_pointwise
  obtain ⟨Cb, hCb, hbp⟩ := GuthMaynard.CitedLV.HB.bprocess
  obtain ⟨Cl, hCl, hlog⟩ := log_pow_five_le (ε / 2) (by positivity)
  set a : ℝ := 4 + 8 * Cd ^ 2 with ha
  set b : ℝ := 20 * Cd ^ 2 * 121 + 3 * Cb ^ 2 * (1 / 10 + 4) with hb
  set c : ℝ := 3 * Cb ^ 2 * (3 * (Cc * 201 ^ 2 * (4 ^ 5 * (Cc * 201 ^ 2 *
    (Cm * 200 ^ (ε / 4)))))) with hc
  have ha0 : 0 < a := by positivity
  have hb0 : 0 < b := by positivity
  have hc0 : 0 < c := by positivity
  refine ⟨a + b * Cl + c * Cl, by positivity, ?_⟩
  intro A T N M hsep hT hT2 hN hNT hM1 hM2
  have hN0 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  have hT1 : (1 : ℝ) ≤ T := by linarith
  obtain ⟨hL1, hL2, hLM, hJ⟩ := log_bounds T hT2 N M hN hNT hM2
  set ℓ := 1 + Real.log T with hℓ
  have hℓ1 : 1 ≤ ℓ := by have := Real.log_nonneg hT1; linarith
  have hX0 : 0 ≤ S A M := S_nonneg A M
  -- the B-process functions
  choose! Lf Mf hL1' hL2' hM' hbd using hbp N hN
  have hbt : ∀ t : ℝ, 10 * N ≤ t → ‖Fsum N (2 * N) t‖ ≤
      Cb * (N / Real.sqrt t * ‖Fsum (Lf t) (Mf t) t‖ + N / Real.sqrt t + Real.log (N * t + 2)) :=
    fun t ht => hbd t ht
  have hb' := bp_abs N Cb Lf Mf hbt
  have hd : ∀ u : ℝ, 1 ≤ |u| → ‖Fsum N (2 * N) u‖ ≤
      Cd * (N / |u| + |u| ^ (1 / 2 : ℝ) * Real.log (|u| + 2)) := fun u hu => hdy N hN u hu
  have hsum := sum_bound A hsep N hN T Cd Cb hCd hCb hd Lf Mf hb' hT
  have hs1 := step1 A N hN
  -- the far pairs
  have hLfprop : ∀ t : ℝ, 10 * N ≤ t →
      t / (8 * Real.pi * N) ≤ Lf t ∧ (Mf t : ℝ) ≤ t / (Real.pi * N) + 1 :=
    fun t ht => ⟨hL2' t ht, hM' t ht⟩
  set B := Cc * (1 + Real.log (M + 1)) ^ 2 *
        (4 ^ 5 * (Cc * (1 + Real.log (M + 1)) ^ 2 * (Cm * (M : ℝ) ^ (ε / 4) * S A M))) with hB
  have hSfar : ∑ x ∈ A, ∑ y ∈ A, (if (10 * N : ℝ) < |x - y| then
        N / |x - y| * ‖Fsum (Lf |x - y|) (Mf |x - y|) (x - y)‖ ^ 2 else 0) ≤
      ((Nat.log 2 ⌈T⌉₊ + 1 : ℕ) : ℝ) * B := by
    calc _ ≤ _ := cover A T N hN hT
          (fun x y => N / |x - y| * ‖Fsum (Lf |x - y|) (Mf |x - y|) (x - y)‖ ^ 2)
          (fun x _ y _ => by positivity)
      _ ≤ ∑ j ∈ range (Nat.log 2 ⌈T⌉₊ + 1), B := Finset.sum_le_sum fun j _ =>
          shell_bound A T N M Cc Cm (ε / 4) hCc hCm hcomp hmono hT hN hM1 Lf Mf hLfprop j
      _ = _ := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  set Sfar := ∑ x ∈ A, ∑ y ∈ A, (if (10 * N : ℝ) < |x - y| then
        N / |x - y| * ‖Fsum (Lf |x - y|) (Mf |x - y|) (x - y)‖ ^ 2 else 0) with hSfardef
  have hSfar0 : 0 ≤ Sfar := by
    refine Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ => ?_
    split_ifs <;> positivity
  have hMε : (M : ℝ) ^ (ε / 4) ≤ 200 ^ (ε / 4) * T ^ (ε / 2) := by
    calc (M : ℝ) ^ (ε / 4) ≤ (200 * T ^ 2) ^ (ε / 4) :=
          Real.rpow_le_rpow (Nat.cast_nonneg _) hM2 (by positivity)
      _ = 200 ^ (ε / 4) * T ^ (ε / 2) := by
        rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_natCast,
          ← Real.rpow_mul (by linarith)]
        congr 2; push_cast; ring
  have hlM0 : 0 ≤ 1 + Real.log (M + 1) := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ M + 1 by
      have := Nat.cast_nonneg (α := ℝ) M; linarith)
    linarith
  have hJB : ((Nat.log 2 ⌈T⌉₊ + 1 : ℕ) : ℝ) * B ≤ (3 * ℓ) * (Cc * (201 * ℓ) ^ 2 *
      (4 ^ 5 * (Cc * (201 * ℓ) ^ 2 * (Cm * (200 ^ (ε / 4) * T ^ (ε / 2)) * S A M)))) := by
    rw [hB]; gcongr
  have hfar : 3 * Cb ^ 2 * Sfar ≤ c * ℓ ^ 5 * T ^ (ε / 2) * S A M := by
    have := mul_le_mul_of_nonneg_left (le_trans hSfar hJB) (by positivity : (0 : ℝ) ≤ 3 * Cb ^ 2)
    refine le_trans this (le_of_eq ?_)
    rw [hc]; ring
  exact final_arith (N : ℝ) (A.card : ℝ) T ε Cd Cb Cl c (S A M) Sfar (S A N)
    (Real.log (10 * N + 2)) (Real.log (N * T + 2)) hε hN0 (Nat.cast_nonneg _) hT1 hX0
    hCd hCb hCl hc0 hL1 hL2 (Real.log_nonneg (by linarith)) (Real.log_nonneg (by nlinarith))
    (hlog T hT1) (le_trans hs1 (mul_le_mul_of_nonneg_left hsum (by positivity))) hfar

end
end GuthMaynard.CitedLV.HB.PartD
end

section
open Finset Complex
namespace GuthMaynard.CitedLV.HB
noncomputable section
/-! ## Part D -/
alias dual := GuthMaynard.CitedLV.HB.PartD.dual

/-! ## Part T -/

end
end GuthMaynard.CitedLV.HB
end


open GuthMaynard in
theorem solution : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ (A : Finset ℝ) (T : ℝ) (N M : ℕ),
    IsSeparated 1 A → (∀ x ∈ A, ∀ y ∈ A, |x - y| ≤ T) → 2 ≤ T → 1 ≤ N → (N : ℝ) ≤ T →
    64 * (T / N + 1) ≤ M → (M : ℝ) ≤ 200 * T ^ 2 →
    (∑ x ∈ A, ∑ y ∈ A, ‖∑ n ∈ Finset.Icc N (2 * N), (((n : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * (n : ℂ) ^ (((x - y : ℝ) : ℂ) * Complex.I)‖ ^ 2) ≤
      C * T ^ ε * ((∑ x ∈ A, ∑ y ∈ A, ‖∑ n ∈ Finset.Icc M (2 * M), (((n : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * (n : ℂ) ^ (((x - y : ℝ) : ℂ) * Complex.I)‖ ^ 2) + (A.card : ℝ) ^ 2 + N * A.card) :=
  GuthMaynard.CitedLV.HB.dual
