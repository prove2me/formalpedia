-- Prove2me | solution 1 for GuthMaynard.van_der_corput_kth_derivative_test
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-15T19:02:48.349297+00:00
-- url     : https://prove2.me/submissions/9307690c-f8f2-43c3-a13a-62064a6ab365

import Definitions.Def_EulerMaclaurin_defs
import Definitions.Def_Fourier_defs
import Definitions.Def_Rectangle_defs
import Definitions.Def_ResidueCalcOnRectangles_defs
import Definitions.Def_ZetaBounds_defs
import Mathlib
import Theorems.Thm_ExponentialSums_vdC_second_derivative
section
namespace GuthMaynard.SubWeyl
/-!
# Blueprint: `μ(1/2) ≤ 27/164` (exponent pair `A B A³ B (0,1) = (11/82, 57/82)`)

Route (Titchmarsh, *The theory of the Riemann zeta-function*, Theorems 5.13 and 4.9; see
`BRIEF.md` next to the copy of this file in the mission folder):

* Part W: Weyl differencing (the A-process) and Abel's inequality;
* Part A: the `k`-th derivative test (Theorem 5.13), by induction on `k`;
* Part B: derivative tests for integrals (Lemmas 4.2, 4.4) and stationary phase (Lemma 4.6);
* Part C: truncated Poisson summation (Lemma 4.7);
* Part T: the B-process (Theorem 4.9);
* Part D: the shifted phase `phi` and its dual phase (calculus);
* Part S: the shifted sums `∑ e(phi t h n)` (B-process, then the fifth-derivative test);
* Part L: the blocks `t^{43/100} ≤ N ≤ t^{1/2}` (A-process and exponent bookkeeping);
* Part M: the blocks `N ≤ t^{43/100}` (trivial bound and fourth-derivative test);
* Part Z: `ζ(1/2+it)` in terms of blocks `∑_{N<n≤N'} n^{it}` with `N ≤ √t`.

Conventions: `e x = exp(2πix)`, written as in `ExponentialSums.vdC_second_derivative`; sums over
`Finset.Ioc a b` with `a b : ℕ`; a function with its derivatives is a tuple of functions with
`HasDerivAt` on the closed interval. Everything after "Assembly" is proved from the stubs.
-/
/-- `e(x) = exp(2πix)`, in the shape of `ExponentialSums.vdC_second_derivative`. -/
noncomputable def e (x : ℝ) : ℂ := Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)

end GuthMaynard.SubWeyl
end

section
namespace GuthMaynard.SubWeyl.PartW
open Finset
/-!
# Part W: Weyl differencing (the A-process) and Abel's inequality
-/
/-- `z` on `(a, b]`, shifted by `H` and extended by zero. -/
noncomputable def ext (z : ℕ → ℂ) (a b H : ℕ) (k : ℕ) : ℂ :=
  if a + H < k ∧ k ≤ b + H then z (k - H) else 0

lemma ext_ne_zero (z : ℕ → ℂ) (a b H k : ℕ) (h : ext z a b H k ≠ 0) :
    (a + H < k ∧ k ≤ b + H) ∧ ext z a b H k = z (k - H) := by
  by_cases hc : a + H < k ∧ k ≤ b + H
  · exact ⟨hc, by simp [ext, hc]⟩
  · exact absurd (by simp [ext, hc]) h

/-- Every window sum of the extension is the full sum. -/
lemma window_sum (z : ℕ → ℂ) (a b H r : ℕ) (hr : r ≤ H) :
    ∑ m ∈ Ioc a (b + H), ext z a b H (m + r) = ∑ n ∈ Ioc a b, z n := by
  symm
  refine Finset.sum_bij_ne_zero (fun n _ _ => n + H - r) ?_ ?_ ?_ ?_
  · intro n hn _
    simp only [mem_Ioc] at hn ⊢
    omega
  · intro n hn _ n' hn' _ h
    simp only [mem_Ioc] at hn hn'
    omega
  · intro m hm hne
    obtain ⟨hc, he⟩ := ext_ne_zero z a b H _ hne
    simp only [mem_Ioc] at hm
    refine ⟨m + r - H, ?_, ?_, ?_⟩
    · simp only [mem_Ioc]
      omega
    · rw [← he]
      exact hne
    · omega
  · intro n hn _
    simp only [mem_Ioc] at hn
    have h1 : n + H - r + r = n + H := by omega
    rw [h1, ext, if_pos (by omega)]
    congr 1
    omega

/-- The correlation of two windows is a shifted correlation of `z`. -/
lemma corr_sum (z : ℕ → ℂ) (a b H r r' : ℕ) (hr : r < H) (hr' : r' ≤ r) :
    ∑ m ∈ Ioc a (b + H), ext z a b H (m + r) * (starRingEnd ℂ) (ext z a b H (m + r')) =
      ∑ n ∈ Ioc a (b - (r - r')), z (n + (r - r')) * (starRingEnd ℂ) (z n) := by
  symm
  refine Finset.sum_bij_ne_zero (fun n _ _ => n + H - r') ?_ ?_ ?_ ?_
  · intro n hn _
    simp only [mem_Ioc] at hn ⊢
    omega
  · intro n hn _ n' hn' _ h
    simp only [mem_Ioc] at hn hn'
    omega
  · intro m hm hne
    have hne1 : ext z a b H (m + r) ≠ 0 := left_ne_zero_of_mul hne
    have hne2 : ext z a b H (m + r') ≠ 0 := by
      intro h0
      apply hne
      rw [h0, map_zero, mul_zero]
    obtain ⟨hc1, he1⟩ := ext_ne_zero z a b H _ hne1
    obtain ⟨hc2, he2⟩ := ext_ne_zero z a b H _ hne2
    simp only [mem_Ioc] at hm
    have e1 : m + r' - H + (r - r') = m + r - H := by omega
    refine ⟨m + r' - H, ?_, ?_, ?_⟩
    · simp only [mem_Ioc]
      omega
    · rw [e1, ← he1, ← he2]
      exact hne
    · omega
  · intro n hn _
    simp only [mem_Ioc] at hn
    have h1 : n + H - r' + r = n + (r - r') + H := by omega
    have h2 : n + H - r' + r' = n + H := by omega
    rw [h1, h2, ext, if_pos (by omega), ext, if_pos (by omega)]
    congr 2
    · omega
    · congr 1
      omega

/-- Counting pairs `(r, r')` by their distance. -/
lemma dist_sum_le (G : ℕ → ℝ) (hG : ∀ h, 0 ≤ G h) (H r : ℕ) (hr : r < H) :
    ∑ r' ∈ range H, (if r' ≤ r then G (r - r') else G (r' - r)) ≤
      G 0 + 2 * ∑ h ∈ Ico 1 H, G h := by
  have hsplit : ∑ r' ∈ range H, (if r' ≤ r then G (r - r') else G (r' - r)) =
      (∑ r' ∈ Ico 0 r, G (r - r') + G 0) + ∑ r' ∈ Ico (r + 1) H, G (r' - r) := by
    rw [Finset.range_eq_Ico, ← Finset.sum_Ico_consecutive _ (Nat.zero_le (r + 1)) (by omega),
      Finset.sum_Ico_succ_top (Nat.zero_le r)]
    congr 1
    · congr 1
      · refine Finset.sum_congr rfl fun r' hr' => ?_
        simp only [mem_Ico] at hr'
        rw [if_pos (by omega)]
      · simp
    · refine Finset.sum_congr rfl fun r' hr' => ?_
      simp only [mem_Ico] at hr'
      rw [if_neg (by omega)]
  have h1 : ∑ r' ∈ Ico 0 r, G (r - r') = ∑ h ∈ Ico 1 (r + 1), G h := by
    refine Finset.sum_nbij' (fun r' => r - r') (fun h => r - h) ?_ ?_ ?_ ?_ ?_
    · intro x hx
      simp only [mem_Ico] at hx ⊢
      omega
    · intro x hx
      simp only [mem_Ico] at hx ⊢
      omega
    · intro x hx
      simp only [mem_Ico] at hx
      show r - (r - x) = x
      omega
    · intro x hx
      simp only [mem_Ico] at hx
      show r - (r - x) = x
      omega
    · intro x _
      rfl
  have h2 : ∑ r' ∈ Ico (r + 1) H, G (r' - r) = ∑ h ∈ Ico 1 (H - r), G h := by
    refine Finset.sum_nbij' (fun r' => r' - r) (fun h => h + r) ?_ ?_ ?_ ?_ ?_
    · intro x hx
      simp only [mem_Ico] at hx ⊢
      omega
    · intro x hx
      simp only [mem_Ico] at hx ⊢
      omega
    · intro x hx
      simp only [mem_Ico] at hx
      show x - r + r = x
      omega
    · intro x hx
      show x + r - r = x
      omega
    · intro x _
      rfl
  have h3 : ∑ h ∈ Ico 1 (r + 1), G h ≤ ∑ h ∈ Ico 1 H, G h :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.Ico_subset_Ico le_rfl (by omega))
      fun i _ _ => hG i
  have h4 : ∑ h ∈ Ico 1 (H - r), G h ≤ ∑ h ∈ Ico 1 H, G h :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.Ico_subset_Ico le_rfl (by omega))
      fun i _ _ => hG i
  rw [hsplit, h1, h2]
  linarith

/-- The sum of the squared window sums. -/
lemma window_sq_sum_le (z : ℕ → ℂ) (a b H : ℕ) :
    ∑ m ∈ Ioc a (b + H), ‖∑ r ∈ range H, ext z a b H (m + r)‖ ^ 2 ≤
      H * (∑ n ∈ Ioc a b, ‖z n‖ ^ 2 +
        2 * ∑ h ∈ Ico 1 H,
          ‖∑ n ∈ Ioc a (b - h), z (n + h) * (starRingEnd ℂ) (z n)‖) := by
  set G : ℕ → ℝ := fun h => ‖∑ n ∈ Ioc a (b - h), z (n + h) * (starRingEnd ℂ) (z n)‖ with hGdef
  set D : ℕ → ℕ → ℂ := fun r r' =>
    ∑ m ∈ Ioc a (b + H), ext z a b H (m + r) * (starRingEnd ℂ) (ext z a b H (m + r')) with hDdef
  have hG0 : G 0 = ∑ n ∈ Ioc a b, ‖z n‖ ^ 2 := by
    have h0 : ∑ n ∈ Ioc a (b - 0), z (n + 0) * (starRingEnd ℂ) (z n) =
        ((∑ n ∈ Ioc a b, ‖z n‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.ofReal_sum]
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [Nat.add_zero, Complex.mul_conj']
      push_cast
      rfl
    show ‖∑ n ∈ Ioc a (b - 0), z (n + 0) * (starRingEnd ℂ) (z n)‖ = _
    rw [h0, Complex.norm_real, Real.norm_of_nonneg (Finset.sum_nonneg fun n _ => by positivity)]
  have hDnorm : ∀ r r', r < H → r' < H →
      ‖D r r'‖ ≤ (if r' ≤ r then G (r - r') else G (r' - r)) := by
    intro r r' hr hr'
    by_cases hle : r' ≤ r
    · rw [if_pos hle]
      show ‖∑ m ∈ Ioc a (b + H), _‖ ≤ _
      rw [corr_sum z a b H r r' hr hle]
    · rw [if_neg hle]
      have hconj : D r r' = (starRingEnd ℂ) (D r' r) := by
        show ∑ m ∈ Ioc a (b + H), _ = (starRingEnd ℂ) (∑ m ∈ Ioc a (b + H), _)
        rw [map_sum]
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [map_mul, Complex.conj_conj, mul_comm]
      rw [hconj, Complex.norm_conj]
      show ‖∑ m ∈ Ioc a (b + H), _‖ ≤ _
      rw [corr_sum z a b H r' r hr' (by omega)]
  have hexp : ((∑ m ∈ Ioc a (b + H), ‖∑ r ∈ range H, ext z a b H (m + r)‖ ^ 2 : ℝ) : ℂ) =
      ∑ r ∈ range H, ∑ r' ∈ range H, D r r' := by
    rw [Complex.ofReal_sum]
    have : ∀ m ∈ Ioc a (b + H),
        ((‖∑ r ∈ range H, ext z a b H (m + r)‖ ^ 2 : ℝ) : ℂ) =
          ∑ r ∈ range H, ∑ r' ∈ range H,
            ext z a b H (m + r) * (starRingEnd ℂ) (ext z a b H (m + r')) := by
      intro m _
      rw [Complex.ofReal_pow, ← Complex.mul_conj', map_sum, Finset.sum_mul_sum]
    rw [Finset.sum_congr rfl this, Finset.sum_comm]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Finset.sum_comm]
  have hnn : 0 ≤ ∑ m ∈ Ioc a (b + H), ‖∑ r ∈ range H, ext z a b H (m + r)‖ ^ 2 :=
    Finset.sum_nonneg fun m _ => by positivity
  have hGnn : ∀ h, 0 ≤ G h := fun h => norm_nonneg _
  calc ∑ m ∈ Ioc a (b + H), ‖∑ r ∈ range H, ext z a b H (m + r)‖ ^ 2
      = ‖((∑ m ∈ Ioc a (b + H), ‖∑ r ∈ range H, ext z a b H (m + r)‖ ^ 2 : ℝ) : ℂ)‖ := by
        rw [Complex.norm_real, Real.norm_of_nonneg hnn]
    _ = ‖∑ r ∈ range H, ∑ r' ∈ range H, D r r'‖ := by rw [hexp]
    _ ≤ ∑ r ∈ range H, ∑ r' ∈ range H, ‖D r r'‖ :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun r _ => norm_sum_le _ _)
    _ ≤ ∑ r ∈ range H, (G 0 + 2 * ∑ h ∈ Ico 1 H, G h) := by
        refine Finset.sum_le_sum fun r hr => ?_
        have hr' : r < H := Finset.mem_range.mp hr
        refine le_trans (Finset.sum_le_sum fun r' hr'' => ?_) (dist_sum_le G hGnn H r hr')
        exact hDnorm r r' hr' (Finset.mem_range.mp hr'')
    _ = H * (∑ n ∈ Ioc a b, ‖z n‖ ^ 2 + 2 * ∑ h ∈ Ico 1 H, G h) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, hG0]

/-- The A-process (Titchmarsh, Lemma 5.10; Graham–Kolesnik, Lemma 2.5), for arbitrary complex
terms. -/
theorem weyl_differencing (z : ℕ → ℂ) (a b H : ℕ) (hH : 1 ≤ H) (hHab : H ≤ b - a) :
    ‖∑ n ∈ Finset.Ioc a b, z n‖ ^ 2 ≤
      2 * ((b : ℝ) - a) / H *
        (∑ n ∈ Finset.Ioc a b, ‖z n‖ ^ 2 +
          2 * ∑ h ∈ Finset.Ico 1 H,
            ‖∑ n ∈ Finset.Ioc a (b - h), z (n + h) * (starRingEnd ℂ) (z n)‖) := by
  set P : ℝ := ∑ n ∈ Finset.Ioc a b, ‖z n‖ ^ 2 +
    2 * ∑ h ∈ Finset.Ico 1 H,
      ‖∑ n ∈ Finset.Ioc a (b - h), z (n + h) * (starRingEnd ℂ) (z n)‖ with hP
  set S : ℂ := ∑ n ∈ Finset.Ioc a b, z n with hS
  have hPnn : 0 ≤ P :=
    add_nonneg (Finset.sum_nonneg fun n _ => by positivity)
      (mul_nonneg (by norm_num) (Finset.sum_nonneg fun h _ => norm_nonneg _))
  have hHpos : (0 : ℝ) < H := by exact_mod_cast hH
  have hHab' : (H : ℝ) ≤ (b : ℝ) - a := by
    have h1 : H + a ≤ b := by omega
    have h2 : ((H + a : ℕ) : ℝ) ≤ b := by exact_mod_cast h1
    push_cast at h2
    linarith
  -- `H • S` is the sum of the window sums
  have h1 : (H : ℂ) * S = ∑ m ∈ Ioc a (b + H), ∑ r ∈ range H, ext z a b H (m + r) := by
    rw [Finset.sum_comm, Finset.sum_congr rfl fun r hr =>
      window_sum z a b H r (Finset.mem_range.mp hr).le, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul]
  have hcard : ((Ioc a (b + H)).card : ℝ) = (b : ℝ) - a + H := by
    rw [Nat.card_Ioc, Nat.cast_sub (by omega)]
    push_cast
    ring
  have h2 : ((H : ℝ) * ‖S‖) ^ 2 ≤ ((b : ℝ) - a + H) * (H * P) := by
    have hn : (H : ℝ) * ‖S‖ = ‖(H : ℂ) * S‖ := by
      rw [norm_mul, Complex.norm_natCast]
    rw [hn, h1]
    calc ‖∑ m ∈ Ioc a (b + H), ∑ r ∈ range H, ext z a b H (m + r)‖ ^ 2
        ≤ (∑ m ∈ Ioc a (b + H), ‖∑ r ∈ range H, ext z a b H (m + r)‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
      _ ≤ ((Ioc a (b + H)).card : ℝ) *
            ∑ m ∈ Ioc a (b + H), ‖∑ r ∈ range H, ext z a b H (m + r)‖ ^ 2 :=
          sq_sum_le_card_mul_sum_sq
      _ ≤ ((b : ℝ) - a + H) * (H * P) := by
          rw [hcard]
          exact mul_le_mul_of_nonneg_left (window_sq_sum_le z a b H) (by linarith)
  have h3 : (H : ℝ) * (‖S‖ ^ 2 * H) ≤ H * (((b : ℝ) - a + H) * P) := by
    calc (H : ℝ) * (‖S‖ ^ 2 * H) = ((H : ℝ) * ‖S‖) ^ 2 := by ring
      _ ≤ ((b : ℝ) - a + H) * (H * P) := h2
      _ = _ := by ring
  have h4 : ‖S‖ ^ 2 * H ≤ ((b : ℝ) - a + H) * P := le_of_mul_le_mul_left h3 hHpos
  rw [div_mul_eq_mul_div, le_div_iff₀ hHpos]
  calc ‖S‖ ^ 2 * H ≤ ((b : ℝ) - a + H) * P := h4
    _ ≤ 2 * ((b : ℝ) - a) * P := mul_le_mul_of_nonneg_right (by linarith) hPnn

end GuthMaynard.SubWeyl.PartW
end

section
namespace GuthMaynard.SubWeyl
/-! ## Part W: Weyl differencing and Abel's inequality -/
alias weyl_differencing := GuthMaynard.SubWeyl.PartW.weyl_differencing

end GuthMaynard.SubWeyl
end

section
namespace GuthMaynard.SubWeyl.PartW
open Finset

end GuthMaynard.SubWeyl.PartW
end

section
namespace GuthMaynard.SubWeyl

end GuthMaynard.SubWeyl
end

section
namespace GuthMaynard.SubWeyl.PartA
open Finset
/-!
# Part A: the `k`-th derivative test (Titchmarsh, Theorem 5.13)

Induction on `k`. Base `k = 2`: `ExponentialSums.vdC_second_derivative` (second differences are
values of `F 2` by the mean value theorem twice; the last term of the sum is peeled off).
Step `k → k+1` (`K = 2^{k-1}`, `α = 1/(2K-2)`, `α' = 1/(4K-2)`): Weyl differencing with
`H = ⌈λ^{-1/(2K-1)}⌉`, the induction hypothesis for the phases `x ↦ F j (x+h) - F j x`
(with `λ` replaced by `hλ`, same `R`), `∑_{h<H} h^α ≤ H·H^α`, `∑_{h<H} h^{-α} ≤ 2H·H^{-α}`.
-/
/-! ### The function `e` -/
lemma e_add (x y : ℝ) : e (x + y) = e x * e y := by
  unfold e
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma conj_e (x : ℝ) : (starRingEnd ℂ) (e x) = e (-x) := by
  unfold e
  rw [← Complex.exp_conj]
  congr 1
  rw [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

lemma norm_e (x : ℝ) : ‖e x‖ = 1 := by
  unfold e
  exact Complex.norm_exp_ofReal_mul_I _

lemma norm_sum_e_le (g : ℕ → ℝ) (a b : ℕ) (hab : a ≤ b) :
    ‖∑ n ∈ Ioc a b, e (g n)‖ ≤ (b : ℝ) - a := by
  calc ‖∑ n ∈ Ioc a b, e (g n)‖ ≤ ∑ n ∈ Ioc a b, ‖e (g n)‖ := norm_sum_le _ _
    _ = (b : ℝ) - a := by simp [norm_e, Nat.cast_sub hab]

lemma norm_sum_e_neg (g : ℕ → ℝ) (s : Finset ℕ) :
    ‖∑ n ∈ s, e (-(g n))‖ = ‖∑ n ∈ s, e (g n)‖ := by
  rw [← Complex.norm_conj (∑ n ∈ s, e (g n)), map_sum]
  simp only [conj_e]

/-! ### Mean value theorem -/
lemma diff_eq (f f' : ℝ → ℝ) (x h : ℝ) (hh : 0 < h)
    (hd : ∀ y ∈ Set.Icc x (x + h), HasDerivAt f (f' y) y) :
    ∃ ξ ∈ Set.Ioo x (x + h), f (x + h) - f x = h * f' ξ := by
  have hlt : x < x + h := by linarith
  obtain ⟨ξ, hξ, hslope⟩ := exists_hasDerivAt_eq_slope f f' hlt
    (fun y hy => (hd y hy).continuousAt.continuousWithinAt)
    (fun y hy => hd y (Set.Ioo_subset_Icc_self hy))
  refine ⟨ξ, hξ, ?_⟩
  have hxh : x + h - x = h := by ring
  rw [hslope, hxh]
  field_simp

/-! ### The statement proved by induction -/
/-- The `k`-th derivative test with constant `C`, with `K` in place of `2^(k-1)`. -/
def TestC (k : ℕ) (K R C : ℝ) : Prop :=
  ∀ (F : ℕ → ℝ → ℝ) (a b : ℕ) (lam σ : ℝ), a < b → 0 < lam →
    (σ = 1 ∨ σ = -1) →
    (∀ j < k, ∀ x ∈ Set.Icc (a : ℝ) b, HasDerivAt (F j) (F (j + 1) x) x) →
    (∀ x ∈ Set.Icc (a : ℝ) b, lam ≤ σ * F k x ∧ σ * F k x ≤ R * lam) →
    ‖∑ n ∈ Finset.Ioc a b, e (F 0 n)‖ ≤
      C * (((b : ℝ) - a) * lam ^ (1 / (2 * K - 2)) +
        ((b : ℝ) - a) ^ (1 - 2 / K) * lam ^ (-(1 / (2 * K - 2))))

def Test (k : ℕ) (K R : ℝ) : Prop := ∃ C : ℝ, 0 < C ∧ TestC k K R C

/-! ### Base case `k = 2` -/
lemma second_diff (F : ℕ → ℝ → ℝ) (a b : ℕ)
    (hd0 : ∀ x ∈ Set.Icc (a : ℝ) b, HasDerivAt (F 0) (F 1 x) x)
    (hd1 : ∀ x ∈ Set.Icc (a : ℝ) b, HasDerivAt (F 1) (F 2 x) x)
    (n : ℕ) (han : a ≤ n) (hnb : n + 2 ≤ b) :
    ∃ η ∈ Set.Icc (a : ℝ) b,
      (F 0 ((n + 1 + 1 : ℕ) : ℝ) - F 0 ((n + 1 : ℕ) : ℝ)) -
        (F 0 ((n + 1 : ℕ) : ℝ) - F 0 (n : ℝ)) = F 2 η := by
  have h1 : (a : ℝ) ≤ n := by exact_mod_cast han
  have h2 : (n : ℝ) + 2 ≤ b := by exact_mod_cast hnb
  obtain ⟨ξ, hξ, e1⟩ := diff_eq (fun x => F 0 (x + 1) - F 0 x) (fun x => F 1 (x + 1) - F 1 x)
    (n : ℝ) 1 one_pos (fun y hy =>
      ((hd0 (y + 1) ⟨by linarith [hy.1], by linarith [hy.2]⟩).comp_add_const y 1).sub
        (hd0 y ⟨by linarith [hy.1], by linarith [hy.2]⟩))
  obtain ⟨η, hη, e2⟩ := diff_eq (F 1) (F 2) ξ 1 one_pos (fun y hy =>
    hd1 y ⟨by linarith [hy.1, hξ.1], by linarith [hy.2, hξ.2]⟩)
  refine ⟨η, ⟨by linarith [hξ.1, hη.1], by linarith [hξ.2, hη.2]⟩, ?_⟩
  simp only [one_mul] at e1 e2
  push_cast
  rw [e1, e2]

lemma base_arith (R L s u : ℝ) (hR : 1 ≤ R) (hL : 0 ≤ L) (hs : 0 < s) (hu : 0 < u)
    (hsu : s * u = 1) :
    8 * (R * L * s + u) + 1 ≤ (8 * R + 1) * ((L + 1) * s + u) := by
  have hsum : 1 ≤ s + u := by
    by_contra hcon
    rw [not_le] at hcon
    nlinarith
  nlinarith [mul_nonneg hL hs.le, mul_nonneg (sub_nonneg.mpr hR) hu.le,
    mul_pos (lt_of_lt_of_le one_pos hR) hs]

theorem base (R : ℝ) (hR : 1 ≤ R) : Test 2 2 R := by
  refine ⟨8 * R + 1, by positivity, ?_⟩
  intro F a b lam σ hab hlam hσ hder hbd
  obtain ⟨m, rfl⟩ : ∃ m, b = m + 1 := ⟨b - 1, by omega⟩
  have ham : a ≤ m := by omega
  have hd0 : ∀ x ∈ Set.Icc (a : ℝ) ((m + 1 : ℕ) : ℝ), HasDerivAt (F 0) (F 1 x) x :=
    hder 0 (by norm_num)
  have hd1 : ∀ x ∈ Set.Icc (a : ℝ) ((m + 1 : ℕ) : ℝ), HasDerivAt (F 1) (F 2 x) x :=
    hder 1 (by norm_num)
  have sd := second_diff F a (m + 1) hd0 hd1
  have key : ‖∑ n ∈ Ioc a m, e (F 0 n)‖ ≤
      8 * (R * ((m : ℝ) - a) * Real.sqrt lam + 1 / Real.sqrt lam) := by
    have hv : ‖∑ n ∈ Ioc a m, e (σ * F 0 n)‖ ≤
        8 * (R * ((m : ℝ) - a) * Real.sqrt lam + 1 / Real.sqrt lam) := by
      refine @ExponentialSums.vdC_second_derivative (fun n => σ * F 0 n) a m lam R ham hlam hR
        ?_ ?_
      · intro n hn1 hn2
        obtain ⟨η, hη, heq⟩ := sd n hn1.le (by omega)
        calc lam ≤ σ * F 2 η := (hbd η hη).1
          _ = _ := by rw [← heq]; ring
      · intro n hn1 hn2
        obtain ⟨η, hη, heq⟩ := sd n hn1.le (by omega)
        calc _ = σ * F 2 η := by rw [← heq]; ring
          _ ≤ R * lam := (hbd η hη).2
    rcases hσ with rfl | rfl
    · simpa using hv
    · simp only [neg_one_mul] at hv
      rwa [norm_sum_e_neg (fun n : ℕ => F 0 n) (Ioc a m)] at hv
  have hs : 0 < Real.sqrt lam := Real.sqrt_pos.mpr hlam
  have hL : (0 : ℝ) ≤ (m : ℝ) - a := by
    have : (a : ℝ) ≤ m := by exact_mod_cast ham
    linarith
  have e1 : (1 : ℝ) / (2 * 2 - 2) = 1 / 2 := by norm_num
  have e2 : (1 : ℝ) - 2 / 2 = 0 := by norm_num
  rw [Finset.sum_Ioc_succ_top ham, e1, e2, Real.rpow_zero, Real.rpow_neg hlam.le,
    ← Real.sqrt_eq_rpow, one_mul]
  calc ‖∑ n ∈ Ioc a m, e (F 0 n) + e (F 0 ((m + 1 : ℕ) : ℝ))‖
      ≤ ‖∑ n ∈ Ioc a m, e (F 0 n)‖ + ‖e (F 0 ((m + 1 : ℕ) : ℝ))‖ := norm_add_le _ _
    _ ≤ 8 * (R * ((m : ℝ) - a) * Real.sqrt lam + (Real.sqrt lam)⁻¹) + 1 := by
        rw [norm_e, ← one_div]
        linarith
    _ ≤ (8 * R + 1) * ((((m : ℝ) - a) + 1) * Real.sqrt lam + (Real.sqrt lam)⁻¹) :=
        base_arith R _ _ _ hR hL hs (inv_pos.mpr hs) (mul_inv_cancel₀ hs.ne')
    _ = _ := by push_cast; ring

/-! ### Sums of powers -/
lemma sum_rpow_le (α : ℝ) (hα : 0 ≤ α) (H : ℕ) :
    ∑ h ∈ Ico 1 H, (h : ℝ) ^ α ≤ H * (H : ℝ) ^ α := by
  calc ∑ h ∈ Ico 1 H, (h : ℝ) ^ α ≤ ∑ _h ∈ Ico 1 H, (H : ℝ) ^ α := by
        refine Finset.sum_le_sum (fun h hh => ?_)
        have : (h : ℝ) ≤ H := by exact_mod_cast (Finset.mem_Ico.mp hh).2.le
        exact Real.rpow_le_rpow (Nat.cast_nonneg _) this hα
    _ = ((H - 1 : ℕ) : ℝ) * (H : ℝ) ^ α := by simp
    _ ≤ H * (H : ℝ) ^ α := by
        refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (Nat.cast_nonneg _) _)
        exact_mod_cast Nat.sub_le H 1

lemma sum_rpow_neg_aux (α : ℝ) (hα : 0 ≤ α) (hα2 : α ≤ 1 / 2) (H : ℕ) :
    ∑ h ∈ Ico 1 (H + 1), (h : ℝ) ^ (-α) ≤ 2 * (H : ℝ) ^ (1 - α) := by
  induction H with
  | zero =>
    simp only [zero_add, Finset.Ico_self, Finset.sum_empty, Nat.cast_zero]
    exact mul_nonneg (by norm_num) (Real.rpow_nonneg le_rfl _)
  | succ H ih =>
    rw [Finset.sum_Ico_succ_top (by omega : 1 ≤ H + 1)]
    have hy : (0 : ℝ) < ((H + 1 : ℕ) : ℝ) := by positivity
    set y : ℝ := ((H + 1 : ℕ) : ℝ) with hydef
    have hHy : (H : ℝ) = y * (1 + -(1 / y)) := by
      rw [hydef]; push_cast; field_simp; ring
    have hy1 : (1 : ℝ) ≤ y := by rw [hydef]; push_cast; linarith [Nat.cast_nonneg (α := ℝ) H]
    have hbern : (1 + -(1 / y)) ^ (1 - α) ≤ 1 + (1 - α) * -(1 / y) := by
      refine rpow_one_add_le_one_add_mul_self ?_ (by linarith) (by linarith)
      have : 1 / y ≤ 1 := by rw [div_le_one hy]; exact hy1
      linarith
    have hnn : (0 : ℝ) ≤ 1 + -(1 / y) := by
      have : 1 / y ≤ 1 := by rw [div_le_one hy]; exact hy1
      linarith
    have hsplit : y ^ (1 - α) = y * y ^ (-α) := by
      rw [sub_eq_add_neg, Real.rpow_add hy, Real.rpow_one]
    have hyα : 0 < y ^ (-α) := Real.rpow_pos_of_pos hy _
    have hH : (H : ℝ) ^ (1 - α) ≤ y * y ^ (-α) * (1 + (1 - α) * -(1 / y)) := by
      rw [hHy, Real.mul_rpow hy.le hnn, hsplit]
      exact mul_le_mul_of_nonneg_left hbern (by positivity)
    have hexp : y * y ^ (-α) * (1 + (1 - α) * -(1 / y)) = y * y ^ (-α) - (1 - α) * y ^ (-α) := by
      field_simp
      ring
    rw [hexp] at hH
    rw [hsplit]
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - 2 * α) hyα.le]

lemma sum_rpow_neg_le (α : ℝ) (hα : 0 ≤ α) (hα2 : α ≤ 1 / 2) (H : ℕ) (hH : 1 ≤ H) :
    ∑ h ∈ Ico 1 H, (h : ℝ) ^ (-α) ≤ 2 * (H * (H : ℝ) ^ (-α)) := by
  have hpos : (0 : ℝ) < H := by exact_mod_cast hH
  calc ∑ h ∈ Ico 1 H, (h : ℝ) ^ (-α) ≤ ∑ h ∈ Ico 1 (H + 1), (h : ℝ) ^ (-α) :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.Ico_subset_Ico le_rfl (Nat.le_succ H))
          (fun h _ _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)
    _ ≤ 2 * (H : ℝ) ^ (1 - α) := sum_rpow_neg_aux α hα hα2 H
    _ = 2 * (H * (H : ℝ) ^ (-α)) := by
        rw [sub_eq_add_neg, Real.rpow_add hpos, Real.rpow_one]

/-! ### The arithmetic of the induction step -/
lemma step_alg2 (C u v X : ℝ) (hC : 0 < C) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (h : X ^ 2 ≤ 2 * u ^ 2 + 8 * C * u ^ 2 + 8 * C * v ^ 2) :
    X ≤ (2 + 8 * C) * (u + v) := by
  have s1 : X ^ 2 ≤ (2 + 8 * C) * (u + v) ^ 2 := by
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 2 + 8 * C) (mul_nonneg hu hv), sq_nonneg v]
  have s2 : (2 + 8 * C) * (u + v) ^ 2 ≤ ((2 + 8 * C) * (u + v)) ^ 2 := by
    have : 0 ≤ ((2 + 8 * C) * (1 + 8 * C)) * (u + v) ^ 2 := by positivity
    nlinarith
  by_contra hcon
  rw [not_le] at hcon
  have hnn : 0 ≤ (2 + 8 * C) * (u + v) := by positivity
  nlinarith

lemma step_alg (C N Hr P Q Nk M A B X : ℝ) (hC : 0 < C) (hN : 0 ≤ N) (hH : 0 < Hr)
    (hA : 0 < A) (hB : 0 < B) (hM : 0 ≤ M)
    (f1 : 1 / Hr ≤ A ^ 2) (f2 : P ≤ 2 * A ^ 2) (f3 : Q ≤ B ^ 2) (f4 : N * Nk = M ^ 2)
    (hX2 : X ^ 2 ≤ 2 * N / Hr * (N + 2 * (Hr * (C * (N * P + 2 * Nk * Q))))) :
    X ≤ (2 + 8 * C) * (N * A + M * B) := by
  have e : 2 * N / Hr * (N + 2 * (Hr * (C * (N * P + 2 * Nk * Q)))) =
      2 * N ^ 2 * (1 / Hr) + 4 * C * N ^ 2 * P + 8 * C * (N * Nk) * Q := by
    field_simp
    ring
  rw [e, f4] at hX2
  have h1 : 2 * N ^ 2 * (1 / Hr) ≤ 2 * N ^ 2 * A ^ 2 :=
    mul_le_mul_of_nonneg_left f1 (by positivity)
  have h2 : 4 * C * N ^ 2 * P ≤ 4 * C * N ^ 2 * (2 * A ^ 2) :=
    mul_le_mul_of_nonneg_left f2 (by positivity)
  have h3 : 8 * C * M ^ 2 * Q ≤ 8 * C * M ^ 2 * B ^ 2 :=
    mul_le_mul_of_nonneg_left f3 (by positivity)
  refine step_alg2 C (N * A) (M * B) X hC (by positivity) (by positivity) ?_
  calc X ^ 2 ≤ 2 * N ^ 2 * (1 / Hr) + 4 * C * N ^ 2 * P + 8 * C * M ^ 2 * Q := hX2
    _ ≤ 2 * N ^ 2 * A ^ 2 + 4 * C * N ^ 2 * (2 * A ^ 2) + 8 * C * M ^ 2 * B ^ 2 := by linarith
    _ = _ := by ring

lemma step_core (K C N lam X : ℝ) (hK : 2 ≤ K) (hC : 0 < C) (hN : 1 ≤ N) (hlam : 0 < lam)
    (hXN : X ≤ N)
    (hW : ∀ H : ℕ, 1 ≤ H → (H : ℝ) ≤ N →
      X ^ 2 ≤ 2 * N / H * (N + 2 * (H * (C *
        (N * (lam ^ (1 / (2 * K - 2)) * (H : ℝ) ^ (1 / (2 * K - 2))) +
          2 * N ^ (1 - 2 / K) *
            (lam ^ (-(1 / (2 * K - 2))) * (H : ℝ) ^ (-(1 / (2 * K - 2))))))))) :
    X ≤ (2 + 8 * C) * (N * lam ^ (1 / (2 * (2 * K) - 2)) +
      N ^ (1 - 2 / (2 * K)) * lam ^ (-(1 / (2 * (2 * K) - 2)))) := by
  have hK0 : K ≠ 0 := by linarith
  have hK1 : 2 * K - 2 ≠ 0 := by linarith
  have hK2 : 2 * K - 1 ≠ 0 := by linarith
  have hK3 : 2 * (2 * K) - 2 ≠ 0 := by linarith
  have E1 : 1 / (2 * K - 1) * (2 * K - 1) = 1 := one_div_mul_cancel hK2
  have E2 : 1 / (2 * K - 2) * (2 * K - 2) = 1 := one_div_mul_cancel hK1
  have E3 : 1 / (2 * (2 * K) - 2) * (2 * (2 * K) - 2) = 1 := one_div_mul_cancel hK3
  have i1 : (1 / (2 * (2 * K) - 2)) * 2 = 1 / (2 * K - 1) := by
    linear_combination (-2 * (1 / (2 * (2 * K) - 2))) * E1 + (1 / (2 * K - 1)) * E3
  have i2 : 1 / (2 * K - 2) + (-(1 / (2 * K - 1))) * (1 / (2 * K - 2)) = 1 / (2 * K - 1) := by
    linear_combination (-(1 / (2 * K - 2))) * E1 + (1 / (2 * K - 1)) * E2
  have i3 : -(1 / (2 * K - 2)) + (-(1 / (2 * K - 1))) * (-(1 / (2 * K - 2))) =
      -(1 / (2 * K - 1)) := by
    linear_combination (1 / (2 * K - 2)) * E1 - (1 / (2 * K - 1)) * E2
  have i4 : 1 + (1 - 2 / K) = (1 - 2 / (2 * K)) * 2 := by
    have : 2 / (2 * K) = 1 / K := by
      rw [div_eq_div_iff (mul_ne_zero two_ne_zero hK0) hK0]
      ring
    rw [this]
    ring
  have hα0 : 0 < 1 / (2 * K - 2) := one_div_pos.mpr (by linarith)
  have hα2 : 1 / (2 * K - 2) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) (by linarith)
  have hα'0 : 0 < 1 / (2 * (2 * K) - 2) := one_div_pos.mpr (by linarith)
  have hβ0 : 0 < 1 / (2 * K - 1) := one_div_pos.mpr (by linarith)
  have hhalf : (1 : ℝ) / 2 ≤ 1 - 2 / (2 * K) := by
    have : 2 / (2 * K) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (by linarith) (by norm_num)]
      linarith
    linarith
  set α := 1 / (2 * K - 2) with hα
  set α' := 1 / (2 * (2 * K) - 2) with hα'
  set β := 1 / (2 * K - 1) with hβ
  set A := lam ^ α' with hAdef
  set B := lam ^ (-α') with hBdef
  set M := N ^ (1 - 2 / (2 * K)) with hMdef
  have hN0 : 0 < N := by linarith
  have hA : 0 < A := Real.rpow_pos_of_pos hlam _
  have hB : 0 < B := Real.rpow_pos_of_pos hlam _
  have hM1 : 1 ≤ M := Real.one_le_rpow hN (by linarith)
  have hM0 : 0 < M := by linarith
  have A2 : A ^ 2 = lam ^ β := by
    rw [hAdef, ← Real.rpow_natCast, ← Real.rpow_mul hlam.le, Nat.cast_ofNat, i1]
  have B2 : B ^ 2 = lam ^ (-β) := by
    rw [hBdef, ← Real.rpow_natCast, ← Real.rpow_mul hlam.le, Nat.cast_ofNat, neg_mul, i1]
  have M2 : N * N ^ (1 - 2 / K) = M ^ 2 := by
    rw [hMdef, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le, Nat.cast_ofNat, ← i4,
      Real.rpow_add hN0, Real.rpow_one]
  have hMB : 0 < M * B := mul_pos hM0 hB
  have hNA : 0 < N * A := mul_pos hN0 hA
  by_cases hl : 1 ≤ lam
  · have hA1 : 1 ≤ A := Real.one_le_rpow hl hα'0.le
    calc X ≤ N := hXN
      _ ≤ N * A := le_mul_of_one_le_right hN0.le hA1
      _ ≤ 1 * (N * A + M * B) := by linarith
      _ ≤ (2 + 8 * C) * (N * A + M * B) :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  · rw [not_le] at hl
    have hH0 : 1 ≤ lam ^ (-β) :=
      Real.one_le_rpow_of_pos_of_le_one_of_nonpos hlam hl.le (by linarith)
    have hH0pos : 0 < lam ^ (-β) := by linarith
    have hH1 : lam ^ (-β) ≤ (⌈lam ^ (-β)⌉₊ : ℝ) := Nat.le_ceil _
    have hH2 : (⌈lam ^ (-β)⌉₊ : ℝ) < lam ^ (-β) + 1 := Nat.ceil_lt_add_one hH0pos.le
    set H : ℕ := ⌈lam ^ (-β)⌉₊ with hHdef
    have hHpos : (0 : ℝ) < H := by linarith
    have h1H : 1 ≤ H := by exact_mod_cast hHpos
    by_cases hHN : (H : ℝ) ≤ N
    · have hX2 := hW H h1H hHN
      have f1 : 1 / (H : ℝ) ≤ A ^ 2 := by
        rw [A2]
        calc 1 / (H : ℝ) ≤ 1 / lam ^ (-β) := one_div_le_one_div_of_le hH0pos hH1
          _ = lam ^ β := by rw [Real.rpow_neg hlam.le, one_div, inv_inv]
      have f2 : lam ^ α * (H : ℝ) ^ α ≤ 2 * A ^ 2 := by
        have h2α : (2 : ℝ) ^ α ≤ 2 := by
          calc (2 : ℝ) ^ α ≤ (2 : ℝ) ^ (1 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
            _ = 2 := Real.rpow_one 2
        have hHa : (H : ℝ) ^ α ≤ 2 * lam ^ (-β * α) := by
          calc (H : ℝ) ^ α ≤ (2 * lam ^ (-β)) ^ α :=
                Real.rpow_le_rpow hHpos.le (by linarith) hα0.le
            _ = (2 : ℝ) ^ α * (lam ^ (-β)) ^ α := Real.mul_rpow (by norm_num) hH0pos.le
            _ = (2 : ℝ) ^ α * lam ^ (-β * α) := by rw [← Real.rpow_mul hlam.le]
            _ ≤ 2 * lam ^ (-β * α) :=
                mul_le_mul_of_nonneg_right h2α (Real.rpow_nonneg hlam.le _)
        calc lam ^ α * (H : ℝ) ^ α ≤ lam ^ α * (2 * lam ^ (-β * α)) :=
              mul_le_mul_of_nonneg_left hHa (Real.rpow_nonneg hlam.le _)
          _ = 2 * lam ^ (α + -β * α) := by rw [Real.rpow_add hlam]; ring
          _ = 2 * A ^ 2 := by rw [i2, A2]
      have f3 : lam ^ (-α) * (H : ℝ) ^ (-α) ≤ B ^ 2 := by
        calc lam ^ (-α) * (H : ℝ) ^ (-α) ≤ lam ^ (-α) * (lam ^ (-β)) ^ (-α) :=
              mul_le_mul_of_nonneg_left
                (Real.antitoneOn_rpow_Ioi_of_exponent_nonpos (by linarith) hH0pos hHpos hH1)
                (Real.rpow_nonneg hlam.le _)
          _ = lam ^ (-α + -β * -α) := by
              rw [Real.rpow_add hlam, ← Real.rpow_mul hlam.le]
          _ = B ^ 2 := by rw [i3, B2]
      exact step_alg C N H _ _ _ M A B X hC hN0.le hHpos hA hB hM0.le f1 f2 f3 M2 hX2
    · rw [not_le] at hHN
      have hNB : N ≤ 2 * B ^ 2 := by rw [B2]; linarith
      have hs1 : Real.sqrt N ≤ M := by
        rw [Real.sqrt_eq_rpow]
        exact Real.rpow_le_rpow_of_exponent_le hN hhalf
      have hs2 : Real.sqrt N ≤ 2 * B := by
        rw [Real.sqrt_le_iff]
        exact ⟨by positivity, by nlinarith [sq_nonneg B]⟩
      calc X ≤ N := hXN
        _ = Real.sqrt N * Real.sqrt N := (Real.mul_self_sqrt hN0.le).symm
        _ ≤ M * (2 * B) := mul_le_mul hs1 hs2 (Real.sqrt_nonneg _) hM0.le
        _ ≤ (2 + 8 * C) * (N * A + M * B) := by
            nlinarith [mul_pos hC hMB, mul_pos hC hNA]

/-! ### The induction step -/
lemma inner_bound (k : ℕ) (K R C : ℝ) (hK : 2 ≤ K) (hC : 0 < C) (ih : TestC k K R C)
    (F : ℕ → ℝ → ℝ) (a b : ℕ) (lam σ : ℝ) (hlam : 0 < lam) (hσ : σ = 1 ∨ σ = -1)
    (hder : ∀ j < k + 1, ∀ x ∈ Set.Icc (a : ℝ) b, HasDerivAt (F j) (F (j + 1) x) x)
    (hbd : ∀ x ∈ Set.Icc (a : ℝ) b, lam ≤ σ * F (k + 1) x ∧ σ * F (k + 1) x ≤ R * lam)
    (h : ℕ) (h1 : 1 ≤ h) (hlt : h < b - a) :
    ‖∑ n ∈ Ioc a (b - h), e (F 0 ((n + h : ℕ) : ℝ)) * (starRingEnd ℂ) (e (F 0 n))‖ ≤
      C * (((b : ℝ) - a) * ((h : ℝ) ^ (1 / (2 * K - 2)) * lam ^ (1 / (2 * K - 2))) +
        ((b : ℝ) - a) ^ (1 - 2 / K) *
          ((h : ℝ) ^ (-(1 / (2 * K - 2))) * lam ^ (-(1 / (2 * K - 2))))) := by
  have hb : h ≤ b := by omega
  have hcast : ((b - h : ℕ) : ℝ) = (b : ℝ) - h := Nat.cast_sub hb
  have hhpos : (0 : ℝ) < h := by exact_mod_cast h1
  have hsum : ∑ n ∈ Ioc a (b - h), e (F 0 ((n + h : ℕ) : ℝ)) * (starRingEnd ℂ) (e (F 0 n)) =
      ∑ n ∈ Ioc a (b - h), e ((fun (j : ℕ) (x : ℝ) => F j (x + h) - F j x) 0 n) := by
    refine Finset.sum_congr rfl (fun n _ => ?_)
    rw [conj_e, ← e_add]
    congr 1
    push_cast
    ring
  rw [hsum]
  have hres := ih (fun (j : ℕ) (x : ℝ) => F j (x + h) - F j x) a (b - h) ((h : ℝ) * lam) σ
    (by omega) (by positivity) hσ ?_ ?_
  · have hL0 : (0 : ℝ) ≤ ((b - h : ℕ) : ℝ) - a := by
      have : (a : ℝ) ≤ ((b - h : ℕ) : ℝ) := by exact_mod_cast (by omega : a ≤ b - h)
      linarith
    have hL : ((b - h : ℕ) : ℝ) - a ≤ (b : ℝ) - a := by rw [hcast]; linarith
    have he : (0 : ℝ) ≤ 1 - 2 / K := by
      have : 2 / K ≤ 1 := by rw [div_le_one (by linarith)]; exact hK
      linarith
    rw [Real.mul_rpow hhpos.le hlam.le, Real.mul_rpow hhpos.le hlam.le] at hres
    refine hres.trans (mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) hC.le)
    · exact mul_le_mul_of_nonneg_right hL (by positivity)
    · exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hL0 hL he) (by positivity)
  · intro j hj x hx
    rw [hcast] at hx
    have d1 := hder j (by omega) (x + h) ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have d2 := hder j (by omega) x ⟨hx.1, by linarith [hx.2]⟩
    exact (d1.comp_add_const x (h : ℝ)).sub d2
  · intro x hx
    rw [hcast] at hx
    obtain ⟨ξ, hξ, heq⟩ := diff_eq (F k) (F (k + 1)) x h hhpos (fun y hy =>
      hder k (Nat.lt_succ_self k) y ⟨by linarith [hx.1, hy.1], by linarith [hx.2, hy.2]⟩)
    have hξm : ξ ∈ Set.Icc (a : ℝ) b := ⟨by linarith [hx.1, hξ.1], by linarith [hx.2, hξ.2]⟩
    have hb1 := (hbd ξ hξm).1
    have hb2 := (hbd ξ hξm).2
    have heq' : σ * (F k (x + h) - F k x) = (h : ℝ) * (σ * F (k + 1) ξ) := by
      rw [heq]; ring
    show (h : ℝ) * lam ≤ σ * (F k (x + h) - F k x) ∧
      σ * (F k (x + h) - F k x) ≤ R * ((h : ℝ) * lam)
    rw [heq']
    constructor
    · exact mul_le_mul_of_nonneg_left hb1 hhpos.le
    · calc (h : ℝ) * (σ * F (k + 1) ξ) ≤ (h : ℝ) * (R * lam) :=
            mul_le_mul_of_nonneg_left hb2 hhpos.le
        _ = R * ((h : ℝ) * lam) := by ring

theorem step (k : ℕ) (K R : ℝ) (hK : 2 ≤ K) (ih : Test k K R) : Test (k + 1) (2 * K) R := by
  obtain ⟨C, hC, ih⟩ := ih
  refine ⟨2 + 8 * C, by positivity, ?_⟩
  intro F a b lam σ hab hlam hσ hder hbd
  have hab' : (a : ℝ) + 1 ≤ b := by exact_mod_cast hab
  have hN : (1 : ℝ) ≤ (b : ℝ) - a := by linarith
  have hα0 : 0 < 1 / (2 * K - 2) := one_div_pos.mpr (by linarith)
  have hα2 : 1 / (2 * K - 2) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) (by linarith)
  refine step_core K C ((b : ℝ) - a) lam _ hK hC hN hlam
    (norm_sum_e_le (fun n : ℕ => F 0 n) a b hab.le) ?_
  intro H h1 hHN
  have hHab : H ≤ b - a := by
    have h' : (H : ℝ) + a ≤ b := by linarith
    have h'' : H + a ≤ b := by exact_mod_cast h'
    omega
  have hHpos : (0 : ℝ) < H := by exact_mod_cast h1
  have w := weyl_differencing (fun n => e (F 0 n)) a b H h1 hHab
  have hsq : ∑ n ∈ Ioc a b, ‖e (F 0 (n : ℝ))‖ ^ 2 = (b : ℝ) - a := by
    simp [norm_e, Nat.cast_sub hab.le]
  set α := 1 / (2 * K - 2) with hα
  have hin : ∑ h ∈ Ico 1 H,
      ‖∑ n ∈ Ioc a (b - h), e (F 0 ((n + h : ℕ) : ℝ)) * (starRingEnd ℂ) (e (F 0 n))‖ ≤
      H * (C * (((b : ℝ) - a) * (lam ^ α * (H : ℝ) ^ α) +
        2 * ((b : ℝ) - a) ^ (1 - 2 / K) * (lam ^ (-α) * (H : ℝ) ^ (-α)))) := by
    have hNk : 0 ≤ ((b : ℝ) - a) ^ (1 - 2 / K) := Real.rpow_nonneg (by linarith) _
    calc _ ≤ ∑ h ∈ Ico 1 H, C * (((b : ℝ) - a) * ((h : ℝ) ^ α * lam ^ α) +
          ((b : ℝ) - a) ^ (1 - 2 / K) * ((h : ℝ) ^ (-α) * lam ^ (-α))) := by
          refine Finset.sum_le_sum (fun h hh => ?_)
          have hh' := Finset.mem_Ico.mp hh
          exact inner_bound k K R C hK hC ih F a b lam σ hlam hσ hder hbd h hh'.1
            (lt_of_lt_of_le hh'.2 hHab)
      _ = C * (((b : ℝ) - a) * lam ^ α * ∑ h ∈ Ico 1 H, (h : ℝ) ^ α +
          ((b : ℝ) - a) ^ (1 - 2 / K) * lam ^ (-α) * ∑ h ∈ Ico 1 H, (h : ℝ) ^ (-α)) := by
          simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl (fun h _ => by ring)
      _ ≤ C * (((b : ℝ) - a) * lam ^ α * (H * (H : ℝ) ^ α) +
          ((b : ℝ) - a) ^ (1 - 2 / K) * lam ^ (-α) * (2 * (H * (H : ℝ) ^ (-α)))) := by
          refine mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) hC.le
          · exact mul_le_mul_of_nonneg_left (sum_rpow_le α hα0.le H)
              (mul_nonneg (by linarith) (Real.rpow_nonneg hlam.le _))
          · exact mul_le_mul_of_nonneg_left (sum_rpow_neg_le α hα0.le hα2 H h1)
              (mul_nonneg hNk (Real.rpow_nonneg hlam.le _))
      _ = _ := by ring
  rw [hsq] at w
  refine w.trans (mul_le_mul_of_nonneg_left (by linarith) ?_)
  exact div_nonneg (by linarith) hHpos.le

theorem test_all (R : ℝ) (hR : 1 ≤ R) (k : ℕ) (hk : 2 ≤ k) :
    Test k ((2 : ℝ) ^ (k - 1)) R ∧ (2 : ℝ) ≤ (2 : ℝ) ^ (k - 1) := by
  induction k, hk using Nat.le_induction with
  | base =>
    refine ⟨?_, by norm_num⟩
    have h2 : (2 : ℝ) ^ (2 - 1) = 2 := by norm_num
    rw [h2]
    exact base R hR
  | succ n hn ih =>
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have hpow : (2 : ℝ) ^ (m + 1 + 1 - 1) = 2 * (2 : ℝ) ^ (m + 1 - 1) := by
      simp only [Nat.add_sub_cancel]
      rw [pow_succ, mul_comm]
    rw [hpow]
    exact ⟨step (m + 1) _ R ih.2 ih.1, by linarith [ih.2]⟩

/-- Titchmarsh, Theorem 5.13 (5.9 for `k = 2`, 5.11 for `k = 3`). `F 0` is the phase and
`F j` its `j`-th derivative on `[a, b]`; `σ = ±1` is the sign of the `k`-th derivative;
`R` is Titchmarsh's `h`. -/
theorem kth_derivative_test (k : ℕ) (hk : 2 ≤ k) (R : ℝ) (hR : 1 ≤ R) :
    ∃ C : ℝ, 0 < C ∧ ∀ (F : ℕ → ℝ → ℝ) (a b : ℕ) (lam σ : ℝ), a < b → 0 < lam →
      (σ = 1 ∨ σ = -1) →
      (∀ j < k, ∀ x ∈ Set.Icc (a : ℝ) b, HasDerivAt (F j) (F (j + 1) x) x) →
      (∀ x ∈ Set.Icc (a : ℝ) b, lam ≤ σ * F k x ∧ σ * F k x ≤ R * lam) →
      ‖∑ n ∈ Finset.Ioc a b, e (F 0 n)‖ ≤
        C * (((b : ℝ) - a) * lam ^ (1 / (2 * (2 : ℝ) ^ (k - 1) - 2)) +
          ((b : ℝ) - a) ^ (1 - 2 / (2 : ℝ) ^ (k - 1)) *
            lam ^ (-(1 / (2 * (2 : ℝ) ^ (k - 1) - 2)))) :=
  (test_all R hR k hk).1

end GuthMaynard.SubWeyl.PartA
end

section
namespace GuthMaynard.SubWeyl
/-! ## Part A: the `k`-th derivative test -/
alias kth_derivative_test := GuthMaynard.SubWeyl.PartA.kth_derivative_test

end GuthMaynard.SubWeyl
end

section
namespace GuthMaynard.SubWeyl.PartB
open MeasureTheory Set
/-!
# Part B: derivative tests for integrals and stationary phase (Titchmarsh, Lemmas 4.2, 4.4, 4.6)
-/
/-! ### The function `e` -/

/-! ### Abel summation and a second mean value bound -/

/-! ### Lemma 4.2 -/

end GuthMaynard.SubWeyl.PartB
end

section
namespace GuthMaynard.SubWeyl
/-! ## Part B: integrals -/

end GuthMaynard.SubWeyl
end

section
namespace GuthMaynard.SubWeyl.PartB
open MeasureTheory Set
/-! ### Monotonicity from derivatives -/

/-! ### Lemma 4.4 -/

end GuthMaynard.SubWeyl.PartB
end

section
namespace GuthMaynard.SubWeyl

end GuthMaynard.SubWeyl
end

section
namespace GuthMaynard.SubWeyl.PartB
open MeasureTheory Set
/-! ### The Fresnel integral -/

/-! ### Taylor's theorem to third order -/

/-! ### Lemma 4.6 -/

end GuthMaynard.SubWeyl.PartB
end

section
namespace GuthMaynard.SubWeyl

end GuthMaynard.SubWeyl
end

section
open Complex Real MeasureTheory intervalIntegral Finset
namespace GuthMaynard.SubWeyl.PartC
open GuthMaynard.SubWeyl
/-!
# Part C: truncated Poisson summation (Titchmarsh, Lemma 4.7 with `η = 1/2`)

Euler–Maclaurin, the Fourier polynomial of the sawtooth with an `L²`-small remainder, the
first-derivative test (`integral_first_deriv_test`) for the frequencies near the range, and the
first-derivative test with the monotone amplitude `f'` for the far frequencies.
-/
/-! ### The sawtooth and its Fourier polynomial -/

/-! ### The `L²` norm of the tail on `[0, 1]` -/

/-! ### The phase `e ∘ f` -/

/-! ### Euler–Maclaurin -/

/-! ### The sawtooth expansion -/

/-! ### The tail term -/

/-! ### The first-derivative test with a monotone amplitude -/

/-! ### Harmonic-type sums -/

/-! ### The normalized case `-1/2 ≤ f'(a) < 1/2` -/

/-! ### The lemma -/

end GuthMaynard.SubWeyl.PartC
end

section
namespace GuthMaynard.SubWeyl
/-! ## Part C: truncated Poisson summation -/

end GuthMaynard.SubWeyl
end

section
namespace GuthMaynard.SubWeyl.PartT
/-!
# Part T: the B-process (Titchmarsh, Theorem 4.9)

`b_process` from `truncated_poisson`, `stationary_phase` and `integral_second_deriv_test`.
-/

end GuthMaynard.SubWeyl.PartT
end

section
namespace GuthMaynard.SubWeyl
/-! ## Part T: the B-process -/

end GuthMaynard.SubWeyl
end

section
namespace GuthMaynard.SubWeyl.PartD
/-!
# Part D: the shifted phase `phi` and its dual phase (calculus)
-/

end GuthMaynard.SubWeyl.PartD
end

section
namespace GuthMaynard.SubWeyl
/-! ## Part D: the shifted phase and its dual -/

end GuthMaynard.SubWeyl
end

section
namespace GuthMaynard.SubWeyl.PartD

end GuthMaynard.SubWeyl.PartD
end

section
namespace GuthMaynard.SubWeyl

end GuthMaynard.SubWeyl
end

section
namespace GuthMaynard.SubWeyl.PartD

end GuthMaynard.SubWeyl.PartD
end

section
namespace GuthMaynard.SubWeyl

end GuthMaynard.SubWeyl
end

section
namespace GuthMaynard.SubWeyl.PartD
/-! ## The dual phase -/

end GuthMaynard.SubWeyl.PartD
end

section
namespace GuthMaynard.SubWeyl

end GuthMaynard.SubWeyl
end

section
namespace GuthMaynard.SubWeyl.PartS
open GuthMaynard.SubWeyl
/-!
# Part S: the shifted sums `∑ e(phi t h n)`

B-process (`b_process`, `R = 10`) on `[N, N']`, reindexing of the dual sum by `m = -ν`,
Abel's inequality (`abel_monotone`) for the amplitude, and the fifth-derivative test
(`kth_derivative_test`, `k = 5`) for the dual phase on `M/26 ≤ μ ≤ M`, `M = th/N²`.
-/
/-! ## Calculus of `phi1`, `phi2`, `xst` -/

/-! ## Reindexing the dual sum -/

/-! ## Monomial identities -/

/-! ## The dual sum -/

/-! ## The stub -/

end GuthMaynard.SubWeyl.PartS
end

section
namespace GuthMaynard.SubWeyl
/-! ## Part S: the shifted sums -/

end GuthMaynard.SubWeyl
end

section
namespace GuthMaynard.SubWeyl.PartL
/-!
# Part L: blocks with `t^{43/100} ≤ N ≤ t^{1/2}` (A-process and exponent bookkeeping)
-/

end GuthMaynard.SubWeyl.PartL
end

section
namespace GuthMaynard.SubWeyl
/-! ## Part L: blocks with `t^{43/100} ≤ N ≤ t^{1/2}` -/

end GuthMaynard.SubWeyl
end

section
namespace GuthMaynard.SubWeyl.PartM
/-!
# Part M: blocks with `N ≤ t^{43/100}` (fourth-derivative test)
-/

end GuthMaynard.SubWeyl.PartM
end

section
namespace GuthMaynard.SubWeyl
/-! ## Part M: blocks with `N ≤ t^{43/100}` -/

end GuthMaynard.SubWeyl
end

section
open Complex Filter Topology Set
namespace GuthMaynard.SubWeyl.PartZ
/-!
# Part Z: `ζ(1/2+it)` in terms of dyadic blocks of `n^{it}` with `N² ≤ t`

`ζ(1/2+it) = ∑_{n ≤ t} n^{-1/2-it} + O(1)` (`Zeta0EqZeta` and Kusmin–Landau, copied from the
mission's `richert_zeta_bound` development); dyadic blocks and Abel's inequality; the blocks with
`N² > t` are turned into blocks with `N² ≤ t` by the B-process
`GuthMaynard.norm_sum_cpow_sub_dual_window_le`.
-/

/-! ## Conjugation -/

/-! ## The dual sum -/

/-! ## Every partial block `(N, R]`, `N ≤ t`, `R ≤ 2N` -/

/-! ## The dyadic decomposition -/

/-! ## The stub -/

end GuthMaynard.SubWeyl.PartZ
end

section
namespace GuthMaynard.SubWeyl
/-! ## Part Z: `ζ(1/2+it)` and blocks of length at most `√t` -/

/-! ## Assembly (no `sorry` below) -/

end GuthMaynard.SubWeyl
end

section
open GuthMaynard
open GuthMaynard.SubWeyl
theorem solution (k : ℕ) (hk : 2 ≤ k) (R : ℝ) (hR : 1 ≤ R) :
    ∃ C : ℝ, 0 < C ∧ ∀ (F : ℕ → ℝ → ℝ) (a b : ℕ) (lam σ : ℝ), a < b → 0 < lam →
      (σ = 1 ∨ σ = -1) →
      (∀ j < k, ∀ x ∈ Set.Icc (a : ℝ) b, HasDerivAt (F j) (F (j + 1) x) x) →
      (∀ x ∈ Set.Icc (a : ℝ) b, lam ≤ σ * F k x ∧ σ * F k x ≤ R * lam) →
      ‖∑ n ∈ Finset.Ioc a b, Complex.exp (((2 * Real.pi * F 0 n : ℝ) : ℂ) * Complex.I)‖ ≤
        C * (((b : ℝ) - a) * lam ^ (1 / (2 * (2 : ℝ) ^ (k - 1) - 2)) +
          ((b : ℝ) - a) ^ (1 - 2 / (2 : ℝ) ^ (k - 1)) *
            lam ^ (-(1 / (2 * (2 : ℝ) ^ (k - 1) - 2)))) :=
  GuthMaynard.SubWeyl.kth_derivative_test k hk R hR
