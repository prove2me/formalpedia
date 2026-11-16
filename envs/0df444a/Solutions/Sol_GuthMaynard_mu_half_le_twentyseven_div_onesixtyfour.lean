-- Prove2me | solution 1 for GuthMaynard.mu_half_le_twentyseven_div_onesixtyfour
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-15T19:02:50.687001+00:00
-- url     : https://prove2.me/submissions/c70c10e2-94a8-4663-b07e-16c201f2c675

import Mathlib
import Theorems.Thm_GuthMaynard_van_der_corput_kth_derivative_test
import Theorems.Thm_GuthMaynard_van_der_corput_b_process
import Definitions.Def_LindelofHypothesis_GrowthAndZeroCounts
import Theorems.Thm_Zeta0EqZeta
import Theorems.Thm_ExponentialSums_kusmin_landau
import Theorems.Thm_GuthMaynard_norm_sum_cpow_sub_dual_window_le

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

/-- The shifted phase: `(n+h)^{it} · conj (n^{it}) = e(phi t h n)`. -/
noncomputable def phi (t : ℝ) (h : ℕ) (x : ℝ) : ℝ :=
  t / (2 * Real.pi) * (Real.log (x + h) - Real.log x)

/-- `phi' = -(th/2π)/(x(x+h))`. -/
noncomputable def phi1 (t : ℝ) (h : ℕ) (x : ℝ) : ℝ :=
  -(t * h / (2 * Real.pi)) / (x * (x + h))

/-- `phi'' = (th/2π)(2x+h)/(x²(x+h)²)`. -/
noncomputable def phi2 (t : ℝ) (h : ℕ) (x : ℝ) : ℝ :=
  t * h / (2 * Real.pi) * (2 * x + h) / (x ^ 2 * (x + h) ^ 2)

/-- `phi''' = (t/π)(1/(x+h)³ - 1/x³)`. -/
noncomputable def phi3 (t : ℝ) (h : ℕ) (x : ℝ) : ℝ :=
  t / Real.pi * (1 / (x + h) ^ 3 - 1 / x ^ 3)

/-- The stationary point: the solution `x > 0` of `phi1 t h x = -μ`, i.e. of
`x (x + h) = th/(2πμ)`. -/
noncomputable def xst (t : ℝ) (h : ℕ) (μ : ℝ) : ℝ :=
  Real.sqrt (t * h / (2 * Real.pi * μ) + (h : ℝ) ^ 2 / 4) - h / 2

/-- The dual phase in the variable `μ = -ν > 0`: `phi(x_ν) - ν x_ν`. -/
noncomputable def dualPhase (t : ℝ) (h : ℕ) (μ : ℝ) : ℝ :=
  phi t h (xst t h μ) + μ * xst t h μ

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
lemma sum_Ioc_eq_sum_range (f : ℕ → ℂ) (a b : ℕ) :
    ∑ n ∈ Ioc a b, f n = ∑ i ∈ range (b - a), f (a + 1 + i) := by
  refine Finset.sum_nbij' (fun n => n - (a + 1)) (fun i => a + 1 + i) ?_ ?_ ?_ ?_ ?_
  · intro x hx
    simp only [mem_Ioc] at hx
    simp only [mem_range]
    omega
  · intro x hx
    simp only [mem_range] at hx
    simp only [mem_Ioc]
    omega
  · intro x hx
    simp only [mem_Ioc] at hx
    show a + 1 + (x - (a + 1)) = x
    omega
  · intro x _
    show a + 1 + x - (a + 1) = x
    omega
  · intro x hx
    simp only [mem_Ioc] at hx
    show f x = f (a + 1 + (x - (a + 1)))
    congr 1
    omega

/-- Abel's inequality with a monotone (either way) nonnegative real amplitude. -/
theorem abel_monotone (g : ℕ → ℝ) (w : ℕ → ℂ) (a b : ℕ) (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hmono : (∀ m n, a < m → m ≤ n → n ≤ b → g m ≤ g n) ∨
      (∀ m n, a < m → m ≤ n → n ≤ b → g n ≤ g m))
    (hg : ∀ n, a < n → n ≤ b → 0 ≤ g n ∧ g n ≤ A)
    (hw : ∀ m, a < m → m ≤ b → ‖∑ n ∈ Finset.Ioc a m, w n‖ ≤ B) :
    ‖∑ n ∈ Finset.Ioc a b, (g n : ℂ) * w n‖ ≤ 2 * A * B := by
  by_cases hab : a < b
  swap
  · rw [Finset.Ioc_eq_empty (by omega), Finset.sum_empty, norm_zero]
    positivity
  set n := b - a with hn
  set G : ℕ → ℝ := fun i => g (a + 1 + i) with hGdef
  set W : ℕ → ℂ := fun i => w (a + 1 + i) with hWdef
  have hGb : ∀ i, i < n → 0 ≤ G i ∧ G i ≤ A := fun i hi => hg _ (by omega) (by omega)
  have hWb : ∀ i, i < n → ‖∑ j ∈ range (i + 1), W j‖ ≤ B := by
    intro i hi
    have h := hw (a + 1 + i) (by omega) (by omega)
    rw [sum_Ioc_eq_sum_range] at h
    have e : a + 1 + i - a = i + 1 := by omega
    rw [e] at h
    exact h
  have hstep : ∑ i ∈ range (n - 1), |G (i + 1) - G i| ≤ 2 * A - G (n - 1) := by
    rcases hmono with hm | hm
    · have : ∑ i ∈ range (n - 1), |G (i + 1) - G i| = ∑ i ∈ range (n - 1), (G (i + 1) - G i) := by
        refine Finset.sum_congr rfl fun i hi => ?_
        have hi' := Finset.mem_range.mp hi
        exact abs_of_nonneg (sub_nonneg.mpr (hm _ _ (by omega) (by omega) (by omega)))
      rw [this, Finset.sum_range_sub]
      have h0 := hGb 0 (by omega)
      have h1 := hGb (n - 1) (by omega)
      linarith [h0.1, h1.2]
    · have : ∑ i ∈ range (n - 1), |G (i + 1) - G i| = ∑ i ∈ range (n - 1), (G i - G (i + 1)) := by
        refine Finset.sum_congr rfl fun i hi => ?_
        have hi' := Finset.mem_range.mp hi
        rw [abs_of_nonpos (sub_nonpos.mpr (hm _ _ (by omega) (by omega) (by omega)))]
        ring
      rw [this, Finset.sum_range_sub']
      have h0 := hGb 0 (by omega)
      have h1 := hGb (n - 1) (by omega)
      linarith [h0.2, h1.2, hA]
  have hrw : ∑ k ∈ Finset.Ioc a b, (g k : ℂ) * w k = ∑ i ∈ range n, G i • W i := by
    rw [sum_Ioc_eq_sum_range]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.real_smul]
  rw [hrw, Finset.sum_range_by_parts]
  have hlast := hGb (n - 1) (by omega)
  have hWlast : ‖∑ i ∈ range n, W i‖ ≤ B := by
    have h := hWb (n - 1) (by omega)
    have e : n - 1 + 1 = n := by omega
    rw [e] at h
    exact h
  calc ‖G (n - 1) • ∑ i ∈ range n, W i -
        ∑ i ∈ range (n - 1), (G (i + 1) - G i) • ∑ j ∈ range (i + 1), W j‖
      ≤ ‖G (n - 1) • ∑ i ∈ range n, W i‖ +
          ‖∑ i ∈ range (n - 1), (G (i + 1) - G i) • ∑ j ∈ range (i + 1), W j‖ := norm_sub_le _ _
    _ ≤ G (n - 1) * B + ∑ i ∈ range (n - 1), |G (i + 1) - G i| * B := by
        refine add_le_add ?_ ((norm_sum_le _ _).trans (Finset.sum_le_sum fun i hi => ?_))
        · rw [norm_smul, Real.norm_of_nonneg hlast.1]
          exact mul_le_mul_of_nonneg_left hWlast hlast.1
        · have hi' := Finset.mem_range.mp hi
          rw [norm_smul, Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_left (hWb i (by omega)) (abs_nonneg _)
    _ = (G (n - 1) + ∑ i ∈ range (n - 1), |G (i + 1) - G i|) * B := by
        rw [← Finset.sum_mul]
        ring
    _ ≤ 2 * A * B := mul_le_mul_of_nonneg_right (by linarith) hB

end GuthMaynard.SubWeyl.PartW
end

section
namespace GuthMaynard.SubWeyl
alias abel_monotone := GuthMaynard.SubWeyl.PartW.abel_monotone

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

/-! ### Mean value theorem -/

/-! ### The statement proved by induction -/

/-! ### Base case `k = 2` -/

/-! ### Sums of powers -/

/-! ### The arithmetic of the induction step -/

/-! ### The induction step -/

end GuthMaynard.SubWeyl.PartA
end

section
namespace GuthMaynard.SubWeyl
/-! ## Part A: the `k`-th derivative test -/
theorem kth_derivative_test (k : ℕ) (hk : 2 ≤ k) (R : ℝ) (hR : 1 ≤ R) :
    ∃ C : ℝ, 0 < C ∧ ∀ (F : ℕ → ℝ → ℝ) (a b : ℕ) (lam σ : ℝ), a < b → 0 < lam →
      (σ = 1 ∨ σ = -1) →
      (∀ j < k, ∀ x ∈ Set.Icc (a : ℝ) b, HasDerivAt (F j) (F (j + 1) x) x) →
      (∀ x ∈ Set.Icc (a : ℝ) b, lam ≤ σ * F k x ∧ σ * F k x ≤ R * lam) →
      ‖∑ n ∈ Finset.Ioc a b, e (F 0 n)‖ ≤
        C * (((b : ℝ) - a) * lam ^ (1 / (2 * (2 : ℝ) ^ (k - 1) - 2)) +
          ((b : ℝ) - a) ^ (1 - 2 / (2 : ℝ) ^ (k - 1)) *
            lam ^ (-(1 / (2 * (2 : ℝ) ^ (k - 1) - 2)))) :=
  GuthMaynard.van_der_corput_kth_derivative_test k hk R hR

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
theorem b_process (R : ℝ) (hR : 1 ≤ R) :
    ∃ κ : ℂ, ∃ C : ℝ, 0 < C ∧ ∀ (f f1 f2 f3 : ℝ → ℝ) (X : ℤ → ℝ) (a b : ℕ) (lam2 lam3 : ℝ),
      a < b → 0 < lam2 → 0 < lam3 →
      (∀ x ∈ Set.Icc (a : ℝ) b, HasDerivAt f (f1 x) x) →
      (∀ x ∈ Set.Icc (a : ℝ) b, HasDerivAt f1 (f2 x) x) →
      (∀ x ∈ Set.Icc (a : ℝ) b, HasDerivAt f2 (f3 x) x) →
      (∀ x ∈ Set.Icc (a : ℝ) b, lam2 ≤ f2 x ∧ f2 x ≤ R * lam2) →
      (∀ x ∈ Set.Icc (a : ℝ) b, |f3 x| ≤ R * lam3) →
      (∀ ν : ℤ, f1 a < ν → (ν : ℝ) ≤ f1 b → X ν ∈ Set.Icc (a : ℝ) b ∧ f1 (X ν) = ν) →
      ‖∑ n ∈ Finset.Ioc a b, e (f n) -
          κ * ∑ ν ∈ Finset.Ioc ⌊f1 a⌋ ⌊f1 b⌋,
            ((f2 (X ν) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
              e (f (X ν) - (ν : ℝ) * X ν)‖ ≤
        C * (lam2 ^ (-(1 / 2 : ℝ)) + Real.log (2 + ((b : ℝ) - a) * lam2) +
          ((b : ℝ) - a) * lam2 ^ (1 / 5 : ℝ) * lam3 ^ (1 / 5 : ℝ)) :=
  GuthMaynard.van_der_corput_b_process R hR

end GuthMaynard.SubWeyl
end

section
namespace GuthMaynard.SubWeyl.PartD
/-!
# Part D: the shifted phase `phi` and its dual phase (calculus)
-/
theorem phi_hasDerivAt (t : ℝ) (h : ℕ) (x : ℝ) (hx : 0 < x) :
    HasDerivAt (phi t h) (phi1 t h x) x ∧ HasDerivAt (phi1 t h) (phi2 t h x) x ∧
      HasDerivAt (phi2 t h) (phi3 t h x) x := by
  have hh : (0 : ℝ) ≤ h := Nat.cast_nonneg h
  have hxh : 0 < x + h := by linarith
  have hx0 : x ≠ 0 := hx.ne'
  have hxh0 : x + h ≠ 0 := hxh.ne'
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hid : HasDerivAt (fun y : ℝ => y + h) 1 x := (hasDerivAt_id x).add_const _
  refine ⟨?_, ?_, ?_⟩
  · have h1 : HasDerivAt (fun y : ℝ => Real.log (y + h)) (1 / (x + h)) x := hid.log hxh0
    have h2 : HasDerivAt (phi t h) _ x :=
      ((h1.sub (Real.hasDerivAt_log hx0)).const_mul (t / (2 * Real.pi)))
    refine h2.congr_deriv ?_
    unfold phi1
    field_simp
    ring
  · have hden : HasDerivAt (fun y : ℝ => y * (y + h)) (1 * (x + h) + x * 1) x :=
      (hasDerivAt_id x).mul hid
    have h2 : HasDerivAt (phi1 t h) _ x :=
      (hasDerivAt_const x (-(t * h / (2 * Real.pi)))).div hden (mul_ne_zero hx0 hxh0)
    refine h2.congr_deriv ?_
    unfold phi2
    field_simp
    ring
  · have hnum : HasDerivAt (fun y : ℝ => t * h / (2 * Real.pi) * (2 * y + h))
        (t * h / (2 * Real.pi) * (2 * 1)) x :=
      (((hasDerivAt_id x).const_mul 2).add_const _).const_mul _
    have hden : HasDerivAt (fun y : ℝ => y ^ 2 * (y + h) ^ 2) _ x :=
      (hasDerivAt_pow 2 x).mul (hid.pow 2)
    have h2 : HasDerivAt (phi2 t h) _ x :=
      hnum.div hden (mul_ne_zero (pow_ne_zero 2 hx0) (pow_ne_zero 2 hxh0))
    refine h2.congr_deriv ?_
    unfold phi3
    simp only [Nat.add_one_sub_one, pow_one, Nat.cast_ofNat]
    field_simp
    ring

end GuthMaynard.SubWeyl.PartD
end

section
namespace GuthMaynard.SubWeyl
/-! ## Part D: the shifted phase and its dual -/
alias phi_hasDerivAt := GuthMaynard.SubWeyl.PartD.phi_hasDerivAt

end GuthMaynard.SubWeyl
end

section
namespace GuthMaynard.SubWeyl.PartD
/-- `λ₂ = th/(26N³)` with ratio `10`, `λ₃ = th/N⁴`. -/
theorem phi_bounds (t : ℝ) (ht : 0 < t) (h N : ℕ) (hh : 1 ≤ h) (hN : 100 * h ≤ N) (x : ℝ)
    (hx1 : (N : ℝ) ≤ x) (hx2 : x ≤ 2 * N) :
    t * h / (26 * (N : ℝ) ^ 3) ≤ phi2 t h x ∧
      phi2 t h x ≤ 10 * (t * h / (26 * (N : ℝ) ^ 3)) ∧
      |phi3 t h x| ≤ t * h / (N : ℝ) ^ 4 := by
  have hh1 : (1 : ℝ) ≤ h := by exact_mod_cast hh
  have hN' : (100 : ℝ) * h ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hx : 0 < x := by linarith
  have hh0 : (0 : ℝ) < h := by linarith
  have hxh : 0 < x + h := by linarith
  have hpi3 : 3 < Real.pi := Real.pi_gt_three
  have hpi4 : Real.pi < 3.15 := Real.pi_lt_d2
  have hpi : 0 < Real.pi := Real.pi_pos
  have hth : 0 < t * h := mul_pos ht hh0
  refine ⟨?_, ?_, ?_⟩
  · -- lower bound
    unfold phi2
    have e1 : t * h / (2 * Real.pi) * (2 * x + h) / (x ^ 2 * (x + h) ^ 2) =
        t * h * ((2 * x + h) / (2 * Real.pi * (x ^ 2 * (x + h) ^ 2))) := by
      field_simp
    rw [e1, div_eq_mul_one_div (t * h)]
    refine mul_le_mul_of_nonneg_left ?_ hth.le
    rw [div_le_div_iff₀ (by positivity) (by positivity), one_mul]
    -- 2π x² (x+h)² ≤ (2x+h) 26 N³ ; x(x+h)² ≤ 2N (2.01N)², 2π·x ≤ 13/4.0401 * ...
    have hxh2 : x + h ≤ 2.01 * N := by linarith
    have a1 : (x + h) ^ 2 ≤ (2.01 * N) ^ 2 := pow_le_pow_left₀ hxh.le hxh2 2
    have a2 : x * (x + h) ^ 2 ≤ 2 * N * (2.01 * N) ^ 2 :=
      mul_le_mul hx2 a1 (by positivity) (by positivity)
    have a3 : 2 * Real.pi * (x * (x + h) ^ 2) ≤ 6.3 * (2 * N * (2.01 * N) ^ 2) :=
      mul_le_mul (by linarith) a2 (by positivity) (by norm_num)
    have a4 : 6.3 * (2 * (N : ℝ) * (2.01 * N) ^ 2) ≤ 2 * (26 * (N : ℝ) ^ 3) := by
      have : (0 : ℝ) ≤ (N : ℝ) ^ 3 := by positivity
      nlinarith
    calc 2 * Real.pi * (x ^ 2 * (x + h) ^ 2) = x * (2 * Real.pi * (x * (x + h) ^ 2)) := by ring
      _ ≤ x * (2 * (26 * (N : ℝ) ^ 3)) := mul_le_mul_of_nonneg_left (a3.trans a4) hx.le
      _ = 2 * x * (26 * (N : ℝ) ^ 3) := by ring
      _ ≤ (2 * x + h) * (26 * (N : ℝ) ^ 3) :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  · unfold phi2
    have e1 : t * h / (2 * Real.pi) * (2 * x + h) / (x ^ 2 * (x + h) ^ 2) =
        t * h * ((2 * x + h) / (2 * Real.pi * (x ^ 2 * (x + h) ^ 2))) := by
      field_simp
    have e2 : 10 * (t * h / (26 * (N : ℝ) ^ 3)) = t * h * (10 / (26 * (N : ℝ) ^ 3)) := by
      ring
    rw [e1, e2]
    refine mul_le_mul_of_nonneg_left ?_ hth.le
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    -- (2x+h) 26 N³ ≤ 10 · 2π x² (x+h)²
    have b1 : (N : ℝ) ^ 2 ≤ x ^ 2 := pow_le_pow_left₀ hN0.le hx1 2
    have b2 : (N : ℝ) ^ 3 ≤ x ^ 2 * (x + h) := by
      calc (N : ℝ) ^ 3 = (N : ℝ) ^ 2 * N := by ring
        _ ≤ x ^ 2 * (x + h) := mul_le_mul b1 (by linarith) hN0.le (by positivity)
    calc (2 * x + h) * (26 * (N : ℝ) ^ 3) ≤ (2 * (x + h)) * (26 * (N : ℝ) ^ 3) :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ ≤ (2 * (x + h)) * (26 * (x ^ 2 * (x + h))) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          linarith
      _ = 52 * (x ^ 2 * (x + h) ^ 2) := by ring
      _ ≤ 10 * (2 * Real.pi * (x ^ 2 * (x + h) ^ 2)) := by
          have : 0 ≤ x ^ 2 * (x + h) ^ 2 := by positivity
          nlinarith
  · unfold phi3
    have e1 : (1 / (x + h) ^ 3 - 1 / x ^ 3) =
        -(h * (3 * x ^ 2 + 3 * x * h + (h : ℝ) ^ 2) / (x ^ 3 * (x + h) ^ 3)) := by
      field_simp
      ring
    rw [e1, mul_neg, abs_neg, abs_of_nonneg (by positivity)]
    have e2 : t / Real.pi * (h * (3 * x ^ 2 + 3 * x * h + (h : ℝ) ^ 2) / (x ^ 3 * (x + h) ^ 3))
        = t * h * ((3 * x ^ 2 + 3 * x * h + (h : ℝ) ^ 2) / (Real.pi * (x ^ 3 * (x + h) ^ 3))) := by
      field_simp
    rw [e2, div_eq_mul_one_div (t * h)]
    refine mul_le_mul_of_nonneg_left ?_ hth.le
    rw [div_le_div_iff₀ (by positivity) (by positivity), one_mul]
    have c1 : (N : ℝ) ^ 3 ≤ x ^ 3 := pow_le_pow_left₀ hN0.le hx1 3
    have c2 : (N : ℝ) ^ 4 ≤ x ^ 3 * (x + h) := by
      calc (N : ℝ) ^ 4 = (N : ℝ) ^ 3 * N := by ring
        _ ≤ x ^ 3 * (x + h) := mul_le_mul c1 (by linarith) hN0.le (by positivity)
    calc (3 * x ^ 2 + 3 * x * h + (h : ℝ) ^ 2) * (N : ℝ) ^ 4
        ≤ (3 * (x + h) ^ 2) * (N : ℝ) ^ 4 := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          nlinarith [mul_pos hx hh0, sq_nonneg (h : ℝ)]
      _ ≤ (3 * (x + h) ^ 2) * (x ^ 3 * (x + h)) :=
          mul_le_mul_of_nonneg_left c2 (by positivity)
      _ = 3 * (x ^ 3 * (x + h) ^ 3) := by ring
      _ ≤ Real.pi * (x ^ 3 * (x + h) ^ 3) :=
          mul_le_mul_of_nonneg_right hpi3.le (by positivity)

end GuthMaynard.SubWeyl.PartD
end

section
namespace GuthMaynard.SubWeyl
alias phi_bounds := GuthMaynard.SubWeyl.PartD.phi_bounds

end GuthMaynard.SubWeyl
end

section
namespace GuthMaynard.SubWeyl.PartD
theorem xst_spec (t : ℝ) (ht : 0 < t) (h : ℕ) (hh : 1 ≤ h) (μ : ℝ) (hμ : 0 < μ) :
    0 < xst t h μ ∧ phi1 t h (xst t h μ) = -μ ∧
      xst t h μ * (xst t h μ + h) = t * h / (2 * Real.pi * μ) := by
  have hh1 : (1 : ℝ) ≤ h := by exact_mod_cast hh
  have hh0 : (0 : ℝ) < h := by linarith
  have hpi : 0 < Real.pi := Real.pi_pos
  have hc : 0 < t * h / (2 * Real.pi * μ) := by positivity
  have hw : 0 ≤ t * h / (2 * Real.pi * μ) + (h : ℝ) ^ 2 / 4 := by positivity
  have hsq := Real.sq_sqrt hw
  have hpos : 0 < xst t h μ := by
    unfold xst
    have : (h : ℝ) / 2 < Real.sqrt (t * h / (2 * Real.pi * μ) + (h : ℝ) ^ 2 / 4) := by
      apply Real.lt_sqrt_of_sq_lt
      nlinarith
    linarith
  have hprod : xst t h μ * (xst t h μ + h) = t * h / (2 * Real.pi * μ) := by
    unfold xst
    nlinarith
  refine ⟨hpos, ?_, hprod⟩
  unfold phi1
  rw [hprod]
  field_simp

end GuthMaynard.SubWeyl.PartD
end

section
namespace GuthMaynard.SubWeyl
alias xst_spec := GuthMaynard.SubWeyl.PartD.xst_spec

end GuthMaynard.SubWeyl
end

section
namespace GuthMaynard.SubWeyl.PartD
/-! ## The dual phase -/
/-- `S μ = √(th/(2πμ) + h²/4) = xst + h/2`. -/
noncomputable def S (t : ℝ) (h : ℕ) (μ : ℝ) : ℝ :=
  Real.sqrt (t * h / (2 * Real.pi * μ) + (h : ℝ) ^ 2 / 4)

/-- `T b k μ = μ^{-b} S(μ)^{-k}`. -/
noncomputable def T (t : ℝ) (h : ℕ) (b k : ℕ) (μ : ℝ) : ℝ :=
  (μ ^ b * S t h μ ^ k)⁻¹

theorem S_pos (t : ℝ) (ht : 0 < t) (h : ℕ) (hh : 1 ≤ h) (μ : ℝ) (hμ : 0 < μ) :
    0 < S t h μ := by
  have hh1 : (1 : ℝ) ≤ h := by exact_mod_cast hh
  have hpi : 0 < Real.pi := Real.pi_pos
  exact Real.sqrt_pos.mpr (by positivity)

theorem S_sq (t : ℝ) (ht : 0 < t) (h : ℕ) (hh : 1 ≤ h) (μ : ℝ) (hμ : 0 < μ) :
    μ * S t h μ ^ 2 = t * h / (2 * Real.pi) + μ * (h : ℝ) ^ 2 / 4 := by
  have hh1 : (1 : ℝ) ≤ h := by exact_mod_cast hh
  have hpi : 0 < Real.pi := Real.pi_pos
  unfold S
  rw [Real.sq_sqrt (by positivity)]
  field_simp

theorem S_hasDerivAt (t : ℝ) (ht : 0 < t) (h : ℕ) (hh : 1 ≤ h) (μ : ℝ) (hμ : 0 < μ) :
    HasDerivAt (S t h) (-(t * h / (2 * Real.pi)) / (2 * μ ^ 2 * S t h μ)) μ := by
  have hh1 : (1 : ℝ) ≤ h := by exact_mod_cast hh
  have hpi : 0 < Real.pi := Real.pi_pos
  have hS := S_pos t ht h hh μ hμ
  have hfun : S t h = fun y : ℝ =>
      Real.sqrt (t * h / (2 * Real.pi) * y⁻¹ + (h : ℝ) ^ 2 / 4) := by
    funext y
    unfold S
    rw [← div_div, div_eq_mul_inv (t * h / (2 * Real.pi)) y]
  have hw : HasDerivAt (fun y : ℝ => t * h / (2 * Real.pi) * y⁻¹ + (h : ℝ) ^ 2 / 4)
      (t * h / (2 * Real.pi) * (-(μ ^ 2)⁻¹)) μ :=
    ((hasDerivAt_inv hμ.ne').const_mul _).add_const _
  have hwpos : t * h / (2 * Real.pi) * μ⁻¹ + (h : ℝ) ^ 2 / 4 ≠ 0 := by positivity
  have h2 := hw.sqrt hwpos
  have hSeq : S t h μ = Real.sqrt (t * h / (2 * Real.pi) * μ⁻¹ + (h : ℝ) ^ 2 / 4) :=
    congrFun hfun μ
  rw [← hfun] at h2
  refine h2.congr_deriv ?_
  rw [hSeq] at hS ⊢
  field_simp

theorem T_hasDerivAt (t : ℝ) (ht : 0 < t) (h : ℕ) (hh : 1 ≤ h) (b k : ℕ) (μ : ℝ)
    (hμ : 0 < μ) :
    HasDerivAt (T t h (b + 1) (k + 1))
      (-((b : ℝ) + 1) * T t h (b + 2) (k + 1) μ +
        (((k : ℝ) + 1) * (t * h / (2 * Real.pi)) / 2) * T t h (b + 3) (k + 3) μ) μ := by
  have hS := S_pos t ht h hh μ hμ
  have hpi : 0 < Real.pi := Real.pi_pos
  have h1 := hasDerivAt_pow (b + 1) μ
  have h2 := (S_hasDerivAt t ht h hh μ hμ).pow (k + 1)
  have h3 : HasDerivAt (T t h (b + 1) (k + 1)) _ μ :=
    (h1.mul h2).inv (mul_ne_zero (pow_ne_zero _ hμ.ne') (pow_ne_zero _ hS.ne'))
  refine h3.congr_deriv ?_
  simp only [Nat.add_sub_cancel, T, Pi.mul_apply, Pi.pow_apply]
  push_cast
  field_simp
  ring

/-- The tuple of derivatives of the dual phase. -/
noncomputable def P (t : ℝ) (h : ℕ) : ℕ → ℝ → ℝ
  | 0 => dualPhase t h
  | 1 => xst t h
  | 2 => fun μ => -(t * h / (2 * Real.pi) / 2) * T t h 2 1 μ
  | 3 => fun μ => (t * h / (2 * Real.pi)) * T t h 3 1 μ -
      ((t * h / (2 * Real.pi)) ^ 2 / 4) * T t h 4 3 μ
  | 4 => fun μ => -(3 * (t * h / (2 * Real.pi))) * T t h 4 1 μ +
      (3 * (t * h / (2 * Real.pi)) ^ 2 / 2) * T t h 5 3 μ -
      (3 * (t * h / (2 * Real.pi)) ^ 3 / 8) * T t h 6 5 μ
  | 5 => fun μ => 12 * (t * h / (2 * Real.pi)) * T t h 5 1 μ -
      9 * (t * h / (2 * Real.pi)) ^ 2 * T t h 6 3 μ +
      (9 / 2) * (t * h / (2 * Real.pi)) ^ 3 * T t h 7 5 μ -
      (15 / 16) * (t * h / (2 * Real.pi)) ^ 4 * T t h 8 7 μ
  | _ => fun _ => 0

theorem P_hasDerivAt (t : ℝ) (ht : 0 < t) (h : ℕ) (hh : 1 ≤ h) (j : ℕ) (hj : j < 5) (μ : ℝ)
    (hμ : 0 < μ) : HasDerivAt (P t h j) (P t h (j + 1) μ) μ := by
  have hS := S_pos t ht h hh μ hμ
  have hSd := S_hasDerivAt t ht h hh μ hμ
  have hx : HasDerivAt (xst t h) (-(t * h / (2 * Real.pi) / 2) * T t h 2 1 μ) μ := by
    have h1 : HasDerivAt (xst t h) _ μ := hSd.sub_const ((h : ℝ) / 2)
    refine h1.congr_deriv ?_
    unfold T
    field_simp
  have hT := fun b k => T_hasDerivAt t ht h hh b k μ hμ
  interval_cases j
  · -- dualPhase
    show HasDerivAt (dualPhase t h) (xst t h μ) μ
    obtain ⟨hpos, hphi1, -⟩ := xst_spec t ht h hh μ hμ
    have hphi := (phi_hasDerivAt t h (xst t h μ) hpos).1
    have h1 := hphi.comp μ hx
    have h2 := (hasDerivAt_id μ).mul hx
    have h3 : HasDerivAt (dualPhase t h) _ μ := h1.add h2
    refine h3.congr_deriv ?_
    rw [hphi1]
    simp only [id]
    ring
  · exact hx
  · show HasDerivAt (fun μ => -(t * h / (2 * Real.pi) / 2) * T t h 2 1 μ) _ μ
    refine HasDerivAt.congr_deriv ((hT 1 0).const_mul (-(t * h / (2 * Real.pi) / 2))) ?_
    show _ = (t * h / (2 * Real.pi)) * T t h 3 1 μ -
      ((t * h / (2 * Real.pi)) ^ 2 / 4) * T t h 4 3 μ
    push_cast
    ring
  · show HasDerivAt (fun μ => (t * h / (2 * Real.pi)) * T t h 3 1 μ -
      ((t * h / (2 * Real.pi)) ^ 2 / 4) * T t h 4 3 μ) _ μ
    refine HasDerivAt.congr_deriv (((hT 2 0).const_mul (t * h / (2 * Real.pi))).sub
      ((hT 3 2).const_mul ((t * h / (2 * Real.pi)) ^ 2 / 4))) ?_
    show _ = -(3 * (t * h / (2 * Real.pi))) * T t h 4 1 μ +
      (3 * (t * h / (2 * Real.pi)) ^ 2 / 2) * T t h 5 3 μ -
      (3 * (t * h / (2 * Real.pi)) ^ 3 / 8) * T t h 6 5 μ
    push_cast
    ring
  · show HasDerivAt (fun μ => -(3 * (t * h / (2 * Real.pi))) * T t h 4 1 μ +
      (3 * (t * h / (2 * Real.pi)) ^ 2 / 2) * T t h 5 3 μ -
      (3 * (t * h / (2 * Real.pi)) ^ 3 / 8) * T t h 6 5 μ) _ μ
    refine HasDerivAt.congr_deriv ((((hT 3 0).const_mul (-(3 * (t * h / (2 * Real.pi))))).add
      ((hT 4 2).const_mul (3 * (t * h / (2 * Real.pi)) ^ 2 / 2))).sub
      ((hT 5 4).const_mul (3 * (t * h / (2 * Real.pi)) ^ 3 / 8))) ?_
    show _ = 12 * (t * h / (2 * Real.pi)) * T t h 5 1 μ -
      9 * (t * h / (2 * Real.pi)) ^ 2 * T t h 6 3 μ +
      (9 / 2) * (t * h / (2 * Real.pi)) ^ 3 * T t h 7 5 μ -
      (15 / 16) * (t * h / (2 * Real.pi)) ^ 4 * T t h 8 7 μ
    push_cast
    ring

theorem rpow_neg_nine_half (μ : ℝ) (hμ : 0 < μ) :
    μ ^ (-(9 / 2 : ℝ)) = Real.sqrt μ / μ ^ 5 := by
  rw [eq_div_iff (by positivity), Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_add hμ]
  norm_num

/-- The polynomial `12 − 9q + (9/2)q² − (15/16)q³` on `[0.99, 1]`. -/
theorem poly_bounds (q : ℝ) (h1 : 99 / 100 ≤ q) (h2 : q ≤ 1) :
    6.5 ≤ 12 - 9 * q + 9 / 2 * q ^ 2 - 15 / 16 * q ^ 3 ∧
      12 - 9 * q + 9 / 2 * q ^ 2 - 15 / 16 * q ^ 3 ≤ 6.6 := by
  obtain ⟨d, rfl⟩ : ∃ d, q = 1 - d := ⟨1 - q, by ring⟩
  have hd0 : 0 ≤ d := by linarith
  have hd1 : d ≤ 1 / 100 := by linarith
  have e : 12 - 9 * (1 - d) + 9 / 2 * (1 - d) ^ 2 - 15 / 16 * (1 - d) ^ 3 =
      105 / 16 + 45 / 16 * d + 27 / 16 * d ^ 2 + 15 / 16 * d ^ 3 := by ring
  rw [e]
  have d2 : d ^ 2 ≤ 1 / 100 * d := by nlinarith
  have d3 : d ^ 3 ≤ 1 / 100 * d := by nlinarith [mul_nonneg hd0 hd0]
  have d2' : 0 ≤ d ^ 2 := by positivity
  have d3' : 0 ≤ d ^ 3 := by positivity
  constructor <;> norm_num <;> linarith

theorem P5_bounds (t : ℝ) (ht : 0 < t) (h : ℕ) (hh : 1 ≤ h) (μ : ℝ) (hμ : 0 < μ)
    (hhμ : h * μ ≤ t / 2000) :
    2 * Real.sqrt (t * h) * μ ^ (-(9 / 2 : ℝ)) ≤ P t h 5 μ ∧
      P t h 5 μ ≤ 3 * Real.sqrt (t * h) * μ ^ (-(9 / 2 : ℝ)) := by
  have hh1 : (1 : ℝ) ≤ h := by exact_mod_cast hh
  have hh0 : (0 : ℝ) < h := by linarith
  have hpi : 0 < Real.pi := Real.pi_pos
  have hpi1 : 3.14 < Real.pi := Real.pi_gt_d2
  have hpi2 : Real.pi < 3.15 := Real.pi_lt_d2
  have hS := S_pos t ht h hh μ hμ
  have hSsq := S_sq t ht h hh μ hμ
  -- abbreviations
  obtain ⟨c, hc⟩ : ∃ c, c = t * h / (2 * Real.pi) := ⟨_, rfl⟩
  obtain ⟨s, hs⟩ : ∃ s, s = S t h μ := ⟨_, rfl⟩
  have hcpos : 0 < c := by rw [hc]; positivity
  have hth : t * h = 2 * Real.pi * c := by rw [hc]; field_simp
  rw [← hc, ← hs] at hSsq
  rw [← hs] at hS
  -- e := μ h² / 4 ≤ c / 100
  have he0 : 0 ≤ μ * (h : ℝ) ^ 2 / 4 := by positivity
  have he1 : μ * (h : ℝ) ^ 2 / 4 ≤ Real.pi / 4000 * c := by
    have : μ * (h : ℝ) ^ 2 ≤ t * h / 2000 := by
      have := mul_le_mul_of_nonneg_right hhμ hh0.le
      nlinarith
    rw [hth] at this
    linarith
  have he2 : μ * (h : ℝ) ^ 2 / 4 ≤ c / 1000 := by
    have : Real.pi / 4000 * c ≤ c / 1000 := by nlinarith
    linarith
  have hD : 0 < μ * s ^ 2 := by positivity
  obtain ⟨q, hq⟩ : ∃ q, q = c / (μ * s ^ 2) := ⟨_, rfl⟩
  have hq1 : q ≤ 1 := by
    rw [hq, div_le_one hD]; linarith
  have hq2 : 99 / 100 ≤ q := by
    rw [hq, le_div_iff₀ hD]; linarith
  obtain ⟨hp1, hp2⟩ := poly_bounds q hq2 hq1
  -- P 5 in closed form
  have hP : P t h 5 μ = c * (12 - 9 * q + 9 / 2 * q ^ 2 - 15 / 16 * q ^ 3) / (μ ^ 5 * s) := by
    show 12 * (t * h / (2 * Real.pi)) * T t h 5 1 μ -
      9 * (t * h / (2 * Real.pi)) ^ 2 * T t h 6 3 μ +
      (9 / 2) * (t * h / (2 * Real.pi)) ^ 3 * T t h 7 5 μ -
      (15 / 16) * (t * h / (2 * Real.pi)) ^ 4 * T t h 8 7 μ = _
    unfold T
    rw [← hc, ← hs, hq]
    field_simp
  -- Y = √(th) √μ s ∈ [2.5 c, 2.6 c]
  obtain ⟨Y, hY⟩ : ∃ Y, Y = Real.sqrt (t * h) * Real.sqrt μ * s := ⟨_, rfl⟩
  have hY0 : 0 < Y := by rw [hY]; positivity
  have hYsq : Y ^ 2 = 2 * Real.pi * c * (c + μ * (h : ℝ) ^ 2 / 4) := by
    rw [hY, mul_pow, mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt hμ.le, hth]
    rw [← hSsq]; ring
  have hc2 : 0 < c ^ 2 := by positivity
  have hY1 : 2.5 * c ≤ Y := by
    apply le_of_sq_le_sq _ hY0.le
    rw [hYsq]
    have : 2 * Real.pi * c * c ≤ 2 * Real.pi * c * (c + μ * (h : ℝ) ^ 2 / 4) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    nlinarith
  have hY2 : Y ≤ 2.6 * c := by
    apply le_of_sq_le_sq _ (by positivity)
    rw [hYsq]
    have : 2 * Real.pi * c * (c + μ * (h : ℝ) ^ 2 / 4) ≤ 2 * Real.pi * c * (c + c / 1000) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    nlinarith
  have hlhs : ∀ a : ℝ, a * Real.sqrt (t * h) * μ ^ (-(9 / 2 : ℝ)) = a * Y / (μ ^ 5 * s) := by
    intro a
    rw [rpow_neg_nine_half μ hμ, hY]
    field_simp
  rw [hlhs, hlhs, hP]
  have hden : 0 < μ ^ 5 * s := by positivity
  constructor
  · apply div_le_div_of_nonneg_right _ hden.le
    nlinarith
  · apply div_le_div_of_nonneg_right _ hden.le
    nlinarith

/-- The dual phase has derivative `xst`, and its fifth derivative is
`≍ (th)^{1/2} μ^{-9/2}` as long as `hμ ≤ t/2000`. -/
theorem dualPhase_derivs :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ ≤ c₂ ∧ ∀ (t : ℝ) (h : ℕ), 0 < t → 1 ≤ h →
      ∃ P : ℕ → ℝ → ℝ, P 0 = dualPhase t h ∧
        (∀ j < 5, ∀ μ : ℝ, 0 < μ → HasDerivAt (P j) (P (j + 1) μ) μ) ∧
        ∀ μ : ℝ, 0 < μ → h * μ ≤ t / 2000 →
          c₁ * Real.sqrt (t * h) * μ ^ (-(9 / 2 : ℝ)) ≤ P 5 μ ∧
            P 5 μ ≤ c₂ * Real.sqrt (t * h) * μ ^ (-(9 / 2 : ℝ)) := by
  refine ⟨2, 3, by norm_num, by norm_num, fun t h ht hh => ⟨P t h, rfl, ?_, ?_⟩⟩
  · exact fun j hj μ hμ => P_hasDerivAt t ht h hh j hj μ hμ
  · exact fun μ hμ hhμ => P5_bounds t ht h hh μ hμ hhμ

end GuthMaynard.SubWeyl.PartD
end

section
namespace GuthMaynard.SubWeyl
alias dualPhase_derivs := GuthMaynard.SubWeyl.PartD.dualPhase_derivs

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
lemma norm_e (x : ℝ) : ‖e x‖ = 1 := by
  unfold e
  exact Complex.norm_exp_ofReal_mul_I _

lemma phi1_neg (t : ℝ) (ht : 0 < t) (h : ℕ) (hh : 1 ≤ h) (x : ℝ) (hx : 0 < x) :
    phi1 t h x < 0 := by
  unfold phi1
  have hh' : (0 : ℝ) < h := by exact_mod_cast hh
  have : 0 < t * h / (2 * Real.pi) / (x * (x + h)) := by positivity
  rw [neg_div]
  linarith

lemma phi1_strictMono (t : ℝ) (ht : 0 < t) (h : ℕ) (hh : 1 ≤ h) (x y : ℝ) (hx : 0 < x)
    (hxy : x < y) : phi1 t h x < phi1 t h y := by
  unfold phi1
  have hh' : (0 : ℝ) < h := by exact_mod_cast hh
  have hc : 0 < t * h / (2 * Real.pi) := by positivity
  have h1 : 0 < x * (x + h) := by positivity
  have h2 : x * (x + h) < y * (y + h) := by nlinarith
  rw [neg_div, neg_div, neg_lt_neg_iff]
  exact div_lt_div_of_pos_left hc h1 h2

/-- A stationary point with `phi1 N < -μ ≤ phi1 N'` lies in `[N, N']`. -/
lemma xst_mem (t : ℝ) (ht : 0 < t) (h : ℕ) (hh : 1 ≤ h) (N N' : ℕ) (hN : 0 < N) (hN' : 0 < N')
    (μ : ℝ) (h1 : phi1 t h N < -μ) (h2 : -μ ≤ phi1 t h N') :
    0 < μ ∧ xst t h μ ∈ Set.Icc (N : ℝ) N' := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hN'r : (0 : ℝ) < N' := by exact_mod_cast hN'
  have hμ : 0 < μ := by
    have := phi1_neg t ht h hh N' hN'r
    linarith
  obtain ⟨hpos, hval, -⟩ := GuthMaynard.SubWeyl.xst_spec t ht h hh μ hμ
  refine ⟨hμ, ?_, ?_⟩
  · by_contra hcon
    rw [not_le] at hcon
    have := phi1_strictMono t ht h hh _ _ hpos hcon
    linarith
  · by_contra hcon
    rw [not_le] at hcon
    have := phi1_strictMono t ht h hh _ _ hN'r hcon
    linarith

lemma neg_phi1_lt (t : ℝ) (ht : 0 < t) (h N : ℕ) (hh : 1 ≤ h) (hN : 0 < N) :
    -phi1 t h N < t * h / (N : ℝ) ^ 2 := by
  unfold phi1
  have hh' : (0 : ℝ) < h := by exact_mod_cast hh
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
  rw [neg_div, neg_neg, div_div]
  apply div_lt_div_of_pos_left (by positivity) (by positivity)
  nlinarith [mul_pos hNr hNr, mul_pos hNr hh']

lemma neg_phi1_ge (t : ℝ) (ht : 0 < t) (h N N' : ℕ) (hh : 1 ≤ h) (hN : 100 * h ≤ N)
    (hN' : 0 < N') (hN'2 : N' ≤ 2 * N) :
    t * h / (N : ℝ) ^ 2 / 26 ≤ -phi1 t h N' := by
  unfold phi1
  have hh' : (0 : ℝ) < h := by exact_mod_cast hh
  have hN'r : (0 : ℝ) < N' := by exact_mod_cast hN'
  have hNh : (100 : ℝ) * h ≤ N := by exact_mod_cast hN
  have hN2 : (N' : ℝ) ≤ 2 * N := by exact_mod_cast hN'2
  have hNr : (0 : ℝ) < N := by linarith
  have hpi : Real.pi < 3.15 := Real.pi_lt_d2
  have hpi0 : (0 : ℝ) < Real.pi := Real.pi_pos
  rw [neg_div, neg_neg, div_div, div_div]
  apply div_le_div_of_nonneg_left (by positivity) (by positivity)
  have e1 : (N' : ℝ) * (N' + h) ≤ 2 * N * (2 * N + N / 100) := by
    apply mul_le_mul hN2 (by linarith) (by positivity) (by positivity)
  have e2 : 2 * Real.pi * ((N' : ℝ) * (N' + h)) ≤ 2 * 3.15 * (2 * N * (2 * N + N / 100)) := by
    apply mul_le_mul (by linarith) e1 (by positivity) (by positivity)
  nlinarith [mul_pos hNr hNr]

lemma h_mul_M_le (t : ℝ) (ht : 0 < t) (h N : ℕ) (hh : 1 ≤ h) (hN : 100 * h ≤ N) :
    (h : ℝ) * (t * h / (N : ℝ) ^ 2) ≤ t / 2000 := by
  have hh' : (0 : ℝ) < h := by exact_mod_cast hh
  have hNh : (100 : ℝ) * h ≤ N := by exact_mod_cast hN
  have hNr : (0 : ℝ) < N := by linarith
  have h2 : (h : ℝ) * h * 2000 ≤ (N : ℝ) ^ 2 := by nlinarith
  rw [← mul_div_assoc, div_le_div_iff₀ (by positivity) (by norm_num)]
  calc (h : ℝ) * (t * h) * 2000 = t * ((h : ℝ) * h * 2000) := by ring
    _ ≤ t * (N : ℝ) ^ 2 := by gcongr

lemma phi2_antitone (t : ℝ) (ht : 0 < t) (h : ℕ) (x y : ℝ) (hx : 0 < x) (hxy : x ≤ y) :
    phi2 t h y ≤ phi2 t h x := by
  have hh' : (0 : ℝ) ≤ h := Nat.cast_nonneg h
  have hy : 0 < y := lt_of_lt_of_le hx hxy
  have key : ∀ z : ℝ, 0 < z → phi2 t h z =
      t * h / (2 * Real.pi) * (1 / z + 1 / (z + h)) * (1 / z * (1 / (z + h))) := by
    intro z hz
    unfold phi2
    have : z + h ≠ 0 := by positivity
    field_simp
    ring
  rw [key x hx, key y hy]
  have hpi0 : (0 : ℝ) < Real.pi := Real.pi_pos
  gcongr

lemma xst_antitone (t : ℝ) (ht : 0 < t) (h : ℕ) (μ₁ μ₂ : ℝ) (h1 : 0 < μ₁) (h12 : μ₁ ≤ μ₂) :
    xst t h μ₂ ≤ xst t h μ₁ := by
  unfold xst
  have hpi0 : (0 : ℝ) < Real.pi := Real.pi_pos
  have hh' : (0 : ℝ) ≤ h := Nat.cast_nonneg h
  gcongr

/-! ## Reindexing the dual sum -/
lemma reindex (G : ℤ → ℂ) (a' b' : ℤ) (A₀ B₀ : ℕ) (hA : (A₀ : ℤ) = -b' - 1)
    (hB : (B₀ : ℤ) = -a' - 1) :
    ∑ ν ∈ Finset.Ioc a' b', G ν = ∑ m ∈ Finset.Ioc A₀ B₀, G (-(m : ℤ)) := by
  apply Finset.sum_nbij' (fun ν : ℤ => (-ν).toNat) (fun m : ℕ => -(m : ℤ))
  · intro ν hν
    simp only [Finset.mem_Ioc] at hν ⊢
    omega
  · intro m hm
    simp only [Finset.mem_Ioc] at hm ⊢
    omega
  · intro ν hν
    simp only [Finset.mem_Ioc] at hν
    show -(((-ν).toNat : ℕ) : ℤ) = ν
    omega
  · intro m hm
    show (-(-(m : ℤ))).toNat = m
    omega
  · intro ν hν
    simp only [Finset.mem_Ioc] at hν
    show G ν = G (-(((-ν).toNat : ℕ) : ℤ))
    congr 1
    omega

/-! ## Monomial identities -/
lemma mono_core1 (a b : ℝ) :
    Real.exp b ^ (3 / 2 : ℝ) * Real.exp a ^ (-(1 / 2 : ℝ)) *
        (Real.exp a / Real.exp b ^ 2 *
          (Real.sqrt (Real.exp a) * (Real.exp a / Real.exp b ^ 2) ^ (-(9 / 2 : ℝ))) ^
            (1 / 30 : ℝ)) =
      Real.exp b ^ (-(1 / 5 : ℝ)) * Real.exp a ^ (11 / 30 : ℝ) := by
  simp only [Real.sqrt_eq_rpow, ← Real.exp_mul, ← Real.exp_nat_mul, ← Real.exp_sub,
    ← Real.exp_add]
  congr 1
  push_cast
  ring

lemma mono_core2 (a b : ℝ) :
    Real.exp b ^ (3 / 2 : ℝ) * Real.exp a ^ (-(1 / 2 : ℝ)) *
        ((Real.exp a / Real.exp b ^ 2) ^ (7 / 8 : ℝ) *
          (Real.sqrt (Real.exp a) * (Real.exp a / Real.exp b ^ 2) ^ (-(9 / 2 : ℝ))) ^
            (-(1 / 30 : ℝ))) =
      Real.exp b ^ (-(11 / 20 : ℝ)) * Real.exp a ^ (61 / 120 : ℝ) := by
  simp only [Real.sqrt_eq_rpow, ← Real.exp_mul, ← Real.exp_nat_mul, ← Real.exp_sub,
    ← Real.exp_add]
  congr 1
  push_cast
  ring

lemma mono_core3 (a b : ℝ) :
    (Real.exp a / Real.exp b ^ 3) ^ (-(1 / 2 : ℝ)) =
      Real.exp b ^ (3 / 2 : ℝ) * Real.exp a ^ (-(1 / 2 : ℝ)) := by
  simp only [← Real.exp_mul, ← Real.exp_nat_mul, ← Real.exp_sub, ← Real.exp_add]
  congr 1
  push_cast
  ring

lemma mono_core4 (a b : ℝ) :
    Real.exp b * (Real.exp a / Real.exp b ^ 3) ^ (1 / 5 : ℝ) *
        (Real.exp a / Real.exp b ^ 4) ^ (1 / 5 : ℝ) =
      Real.exp a ^ (2 / 5 : ℝ) * Real.exp b ^ (-(2 / 5 : ℝ)) := by
  simp only [← Real.exp_mul, ← Real.exp_nat_mul, ← Real.exp_sub, ← Real.exp_add]
  congr 1
  push_cast
  ring

/-- `c₁^{1/30} N^{-1/5} T^{11/30}`. -/
lemma mono1 (T n c₁ : ℝ) (hT : 0 < T) (hn : 0 < n) (hc : 0 < c₁) :
    n ^ (3 / 2 : ℝ) * T ^ (-(1 / 2 : ℝ)) *
        (T / n ^ 2 * (c₁ * Real.sqrt T * (T / n ^ 2) ^ (-(9 / 2 : ℝ))) ^ (1 / 30 : ℝ)) =
      c₁ ^ (1 / 30 : ℝ) * (n ^ (-(1 / 5 : ℝ)) * T ^ (11 / 30 : ℝ)) := by
  obtain ⟨a, rfl⟩ : ∃ a, T = Real.exp a := ⟨Real.log T, (Real.exp_log hT).symm⟩
  obtain ⟨b, rfl⟩ : ∃ b, n = Real.exp b := ⟨Real.log n, (Real.exp_log hn).symm⟩
  rw [← mono_core1 a b, mul_assoc c₁, Real.mul_rpow hc.le (by positivity)]
  ring

lemma mono2 (T n c₁ : ℝ) (hT : 0 < T) (hn : 0 < n) (hc : 0 < c₁) :
    n ^ (3 / 2 : ℝ) * T ^ (-(1 / 2 : ℝ)) *
        ((T / n ^ 2) ^ (7 / 8 : ℝ) *
          (c₁ * Real.sqrt T * (T / n ^ 2) ^ (-(9 / 2 : ℝ))) ^ (-(1 / 30 : ℝ))) =
      c₁ ^ (-(1 / 30 : ℝ)) * (n ^ (-(11 / 20 : ℝ)) * T ^ (61 / 120 : ℝ)) := by
  obtain ⟨a, rfl⟩ : ∃ a, T = Real.exp a := ⟨Real.log T, (Real.exp_log hT).symm⟩
  obtain ⟨b, rfl⟩ : ∃ b, n = Real.exp b := ⟨Real.log n, (Real.exp_log hn).symm⟩
  rw [← mono_core2 a b, mul_assoc c₁, Real.mul_rpow hc.le (by positivity)]
  ring

/-- `λ₂^{-1/2} ≤ 6 N^{3/2} T^{-1/2}`. -/
lemma mono3 (T n : ℝ) (hT : 0 < T) (hn : 0 < n) :
    (T / (26 * n ^ 3)) ^ (-(1 / 2 : ℝ)) ≤ 6 * (n ^ (3 / 2 : ℝ) * T ^ (-(1 / 2 : ℝ))) := by
  obtain ⟨a, rfl⟩ : ∃ a, T = Real.exp a := ⟨Real.log T, (Real.exp_log hT).symm⟩
  obtain ⟨b, rfl⟩ : ∃ b, n = Real.exp b := ⟨Real.log n, (Real.exp_log hn).symm⟩
  have h26 : ((1 : ℝ) / 26) ^ (-(1 / 2 : ℝ)) ≤ 6 := by
    rw [Real.rpow_neg (by norm_num), ← Real.sqrt_eq_rpow, one_div, Real.sqrt_inv, inv_inv]
    rw [show (6 : ℝ) = Real.sqrt 36 by
      rw [show (36 : ℝ) = 6 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hsplit : Real.exp a / (26 * Real.exp b ^ 3) = 1 / 26 * (Real.exp a / Real.exp b ^ 3) := by
    field_simp
  rw [hsplit, Real.mul_rpow (by norm_num) (by positivity), mono_core3 a b]
  have : 0 ≤ Real.exp b ^ (3 / 2 : ℝ) * Real.exp a ^ (-(1 / 2 : ℝ)) := by positivity
  exact mul_le_mul_of_nonneg_right h26 this

/-- `N λ₂^{1/5} λ₃^{1/5} ≤ T^{2/5} N^{-2/5}`. -/
lemma mono4 (T n : ℝ) (hT : 0 < T) (hn : 0 < n) :
    n * (T / (26 * n ^ 3)) ^ (1 / 5 : ℝ) * (T / n ^ 4) ^ (1 / 5 : ℝ) ≤
      T ^ (2 / 5 : ℝ) * n ^ (-(2 / 5 : ℝ)) := by
  have hle : (T / (26 * n ^ 3)) ^ (1 / 5 : ℝ) ≤ (T / n ^ 3) ^ (1 / 5 : ℝ) := by
    apply Real.rpow_le_rpow (by positivity) _ (by norm_num)
    apply div_le_div_of_nonneg_left hT.le (by positivity)
    nlinarith [pow_pos hn 3]
  obtain ⟨a, rfl⟩ : ∃ a, T = Real.exp a := ⟨Real.log T, (Real.exp_log hT).symm⟩
  obtain ⟨b, rfl⟩ : ∃ b, n = Real.exp b := ⟨Real.log n, (Real.exp_log hn).symm⟩
  rw [← mono_core4 a b]
  gcongr

/-- The ratio constant for the fifth-derivative test on `M/26 ≤ μ ≤ M`. -/
lemma ratio_lam (c₁ c₂ s M : ℝ) (hc : 0 < c₁) (hM : 0 < M) :
    c₂ * s * (M / 26) ^ (-(9 / 2 : ℝ)) =
      c₂ / c₁ * (26 : ℝ) ^ (9 / 2 : ℝ) * (c₁ * s * M ^ (-(9 / 2 : ℝ))) := by
  rw [Real.div_rpow hM.le (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 26)]
  field_simp

lemma log_term (t T n d : ℝ) (ht : 2 ≤ t) (hn : 1 ≤ n) (hTt : T ≤ t * t) (hT : 0 < T)
    (hd0 : 0 ≤ d) (hd : d ≤ n) :
    Real.log (2 + d * (T / (26 * n ^ 3))) ≤ 2 * Real.log t := by
  have h1 : d * (T / (26 * n ^ 3)) ≤ T / 26 := by
    rw [← mul_div_assoc, div_le_div_iff₀ (by positivity) (by norm_num)]
    have : d * 26 ≤ 26 * n ^ 3 := by nlinarith [pow_le_pow_left₀ zero_le_one hn 3, sq_nonneg n]
    calc d * T * 26 = T * (d * 26) := by ring
      _ ≤ T * (26 * n ^ 3) := by gcongr
  have h2 : 2 + d * (T / (26 * n ^ 3)) ≤ t ^ 2 := by nlinarith
  have h3 : 0 < 2 + d * (T / (26 * n ^ 3)) := by positivity
  calc Real.log (2 + d * (T / (26 * n ^ 3))) ≤ Real.log (t ^ 2) := Real.log_le_log h3 h2
    _ = 2 * Real.log t := by rw [Real.log_pow]; norm_num

/-! ## The dual sum -/
/-- Abel's inequality and the fifth-derivative test on the dual sum; `h5` is
`kth_derivative_test` with `k = 5` and `R = c₂/c₁ · 26^{9/2}`. -/
lemma dual_sum_bound (c₁ c₂ C5 : ℝ) (hc₁ : 0 < c₁) (hC5 : 0 < C5)
    (h5 : ∀ (F : ℕ → ℝ → ℝ) (a b : ℕ) (lam σ : ℝ), a < b → 0 < lam →
      (σ = 1 ∨ σ = -1) →
      (∀ j < 5, ∀ x ∈ Set.Icc (a : ℝ) b, HasDerivAt (F j) (F (j + 1) x) x) →
      (∀ x ∈ Set.Icc (a : ℝ) b, lam ≤ σ * F 5 x ∧
        σ * F 5 x ≤ c₂ / c₁ * (26 : ℝ) ^ (9 / 2 : ℝ) * lam) →
      ‖∑ n ∈ Finset.Ioc a b, e (F 0 n)‖ ≤
        C5 * (((b : ℝ) - a) * lam ^ (1 / (2 * (2 : ℝ) ^ (5 - 1) - 2)) +
          ((b : ℝ) - a) ^ (1 - 2 / (2 : ℝ) ^ (5 - 1)) *
            lam ^ (-(1 / (2 * (2 : ℝ) ^ (5 - 1) - 2)))))
    (t : ℝ) (ht : 0 < t) (h N N' : ℕ) (hh : 1 ≤ h) (hN : 100 * h ≤ N) (hNN' : N < N')
    (hN'2 : N' ≤ 2 * N) (P : ℕ → ℝ → ℝ) (hP0 : P 0 = dualPhase t h)
    (hPd : ∀ j < 5, ∀ μ : ℝ, 0 < μ → HasDerivAt (P j) (P (j + 1) μ) μ)
    (hP5 : ∀ μ : ℝ, 0 < μ → h * μ ≤ t / 2000 →
      c₁ * Real.sqrt (t * h) * μ ^ (-(9 / 2 : ℝ)) ≤ P 5 μ ∧
        P 5 μ ≤ c₂ * Real.sqrt (t * h) * μ ^ (-(9 / 2 : ℝ))) :
    ‖∑ ν ∈ Finset.Ioc ⌊phi1 t h N⌋ ⌊phi1 t h N'⌋,
        ((phi2 t h (xst t h (-(ν : ℝ))) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
          e (phi t h (xst t h (-(ν : ℝ))) - (ν : ℝ) * xst t h (-(ν : ℝ)))‖ ≤
      2 * (t * h / (26 * (N : ℝ) ^ 3)) ^ (-(1 / 2 : ℝ)) *
        (1 + C5 * (t * h / (N : ℝ) ^ 2 *
            (c₁ * Real.sqrt (t * h) * (t * h / (N : ℝ) ^ 2) ^ (-(9 / 2 : ℝ))) ^ (1 / 30 : ℝ) +
          (t * h / (N : ℝ) ^ 2) ^ (7 / 8 : ℝ) *
            (c₁ * Real.sqrt (t * h) * (t * h / (N : ℝ) ^ 2) ^ (-(9 / 2 : ℝ))) ^
              (-(1 / 30 : ℝ)))) := by
  have hNpos : 0 < N := by omega
  have hN'pos : 0 < N' := by omega
  have hh' : (0 : ℝ) < h := by exact_mod_cast hh
  have hNr : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hN'r : (0 : ℝ) < N' := by exact_mod_cast hN'pos
  have hN2r : (N' : ℝ) ≤ 2 * N := by exact_mod_cast hN'2
  have hNN'r : (N : ℝ) ≤ N' := by exact_mod_cast hNN'.le
  have hT : 0 < t * h := by positivity
  set M : ℝ := t * h / (N : ℝ) ^ 2 with hMdef
  have hM : 0 < M := by positivity
  set lam : ℝ := c₁ * Real.sqrt (t * h) * M ^ (-(9 / 2 : ℝ)) with hlamdef
  have hlam : 0 < lam := by positivity
  set lam2 : ℝ := t * h / (26 * (N : ℝ) ^ 3) with hlam2def
  have hlam2 : 0 < lam2 := by positivity
  set a' : ℤ := ⌊phi1 t h N⌋ with ha'def
  set b' : ℤ := ⌊phi1 t h N'⌋ with hb'def
  have ha' : a' < 0 := Int.floor_lt.mpr (by simpa using phi1_neg t ht h hh N hNr)
  have hb' : b' < 0 := Int.floor_lt.mpr (by simpa using phi1_neg t ht h hh N' hN'r)
  set A₀ : ℕ := (-b' - 1).toNat with hA₀def
  set B₀ : ℕ := (-a' - 1).toNat with hB₀def
  have hA : (A₀ : ℤ) = -b' - 1 := Int.toNat_of_nonneg (by omega)
  have hB : (B₀ : ℤ) = -a' - 1 := Int.toNat_of_nonneg (by omega)
  have hAr : (A₀ : ℝ) = -(b' : ℝ) - 1 := by exact_mod_cast hA
  have hBr : (B₀ : ℝ) = -(a' : ℝ) - 1 := by exact_mod_cast hB
  -- the range of `μ`
  have hrange : ∀ μ : ℝ, (A₀ : ℝ) + 1 ≤ μ → μ ≤ B₀ →
      0 < μ ∧ xst t h μ ∈ Set.Icc (N : ℝ) N' ∧ M / 26 ≤ μ ∧ μ < M := by
    intro μ h1 h2
    have e1 : phi1 t h N < -μ := by
      have := Int.lt_floor_add_one (phi1 t h N)
      linarith
    have e2 : -μ ≤ phi1 t h N' := by
      have := Int.floor_le (phi1 t h N')
      linarith
    obtain ⟨hμ, hmem⟩ := xst_mem t ht h hh N N' hNpos hN'pos μ e1 e2
    refine ⟨hμ, hmem, ?_, ?_⟩
    · have := neg_phi1_ge t ht h N N' hh hN hN'pos hN'2
      linarith
    · have := neg_phi1_lt t ht h N hh hNpos
      linarith
  have hphi2 : ∀ μ : ℝ, (A₀ : ℝ) + 1 ≤ μ → μ ≤ B₀ → lam2 ≤ phi2 t h (xst t h μ) := by
    intro μ h1 h2
    obtain ⟨-, hmem, -, -⟩ := hrange μ h1 h2
    exact (GuthMaynard.SubWeyl.phi_bounds t ht h N hh hN _ hmem.1 (le_trans hmem.2 hN2r)).1
  -- reindex
  rw [reindex _ a' b' A₀ B₀ hA hB]
  have hsum : ∑ m ∈ Finset.Ioc A₀ B₀,
      ((phi2 t h (xst t h (-(((-(m : ℤ) : ℤ)) : ℝ))) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
        e (phi t h (xst t h (-(((-(m : ℤ) : ℤ)) : ℝ))) -
          (((-(m : ℤ) : ℤ)) : ℝ) * xst t h (-(((-(m : ℤ) : ℤ)) : ℝ))) =
      ∑ m ∈ Finset.Ioc A₀ B₀,
        (((fun m : ℕ => phi2 t h (xst t h (m : ℝ)) ^ (-(1 / 2 : ℝ))) m : ℝ) : ℂ) *
          (fun m : ℕ => e (dualPhase t h (m : ℝ))) m := by
    refine Finset.sum_congr rfl (fun m _ => ?_)
    have hm : -(((-(m : ℤ) : ℤ)) : ℝ) = (m : ℝ) := by push_cast; ring
    have hm' : (((-(m : ℤ) : ℤ)) : ℝ) = -(m : ℝ) := by push_cast; ring
    rw [hm, hm']
    show _ * e _ = _ * e (dualPhase t h (m : ℝ))
    unfold dualPhase
    congr 2
    ring
  rw [hsum]
  have hB1 : (0 : ℝ) ≤ 1 + C5 * (M * lam ^ (1 / 30 : ℝ) +
      M ^ (7 / 8 : ℝ) * lam ^ (-(1 / 30 : ℝ))) := by positivity
  refine GuthMaynard.SubWeyl.abel_monotone _ _ A₀ B₀ (lam2 ^ (-(1 / 2 : ℝ))) _ (by positivity) hB1 (Or.inr ?_) ?_ ?_
  · -- antitone amplitude
    intro m n hm hmn hn
    have hm1 : (A₀ : ℝ) + 1 ≤ m := by exact_mod_cast hm
    have hn1 : (A₀ : ℝ) + 1 ≤ n := by exact_mod_cast (lt_of_lt_of_le hm hmn)
    have hm2 : (m : ℝ) ≤ B₀ := by exact_mod_cast (le_trans hmn hn)
    have hn2 : (n : ℝ) ≤ B₀ := by exact_mod_cast hn
    have hmnr : (m : ℝ) ≤ n := by exact_mod_cast hmn
    obtain ⟨hmpos, -, -, -⟩ := hrange m hm1 hm2
    obtain ⟨hnpos, hnmem, -, -⟩ := hrange n hn1 hn2
    have hxn : 0 < xst t h n := lt_of_lt_of_le hNr hnmem.1
    have h1 : xst t h n ≤ xst t h m := xst_antitone t ht h _ _ hmpos hmnr
    have h2 : phi2 t h (xst t h m) ≤ phi2 t h (xst t h n) := phi2_antitone t ht h _ _ hxn h1
    have h3 : 0 < phi2 t h (xst t h m) := lt_of_lt_of_le hlam2 (hphi2 m hm1 hm2)
    exact Real.rpow_le_rpow_of_nonpos h3 h2 (by norm_num)
  · intro n hn1 hn2
    have hn1' : (A₀ : ℝ) + 1 ≤ n := by exact_mod_cast hn1
    have hn2' : (n : ℝ) ≤ B₀ := by exact_mod_cast hn2
    have h3 := hphi2 n hn1' hn2'
    exact ⟨Real.rpow_nonneg (le_trans hlam2.le h3) _,
      Real.rpow_le_rpow_of_nonpos hlam2 h3 (by norm_num)⟩
  · -- partial sums
    intro m hm1 hm2
    have hm2' : (m : ℝ) ≤ B₀ := by exact_mod_cast hm2
    have hmM : (m : ℝ) < M := by
      have hm1' : (A₀ : ℝ) + 1 ≤ m := by exact_mod_cast hm1
      exact (hrange m hm1' hm2').2.2.2
    rw [← Finset.sum_Ioc_consecutive _ (Nat.le_succ A₀) (Nat.succ_le_of_lt hm1),
      Nat.Ioc_succ_singleton, Finset.sum_singleton]
    refine le_trans (norm_add_le _ _) (add_le_add (norm_e _).le ?_)
    rcases eq_or_lt_of_le (Nat.succ_le_of_lt hm1) with heq | hlt
    · rw [← heq]
      simp only [Finset.Ioc_self, Finset.sum_empty, norm_zero]
      positivity
    · have e1 : (1 / (2 * (2 : ℝ) ^ (5 - 1) - 2)) = 1 / 30 := by norm_num
      have e2 : (1 - 2 / (2 : ℝ) ^ (5 - 1)) = 7 / 8 := by norm_num
      have key := h5 P (A₀ + 1) m lam 1 hlt hlam (Or.inl rfl) ?_ ?_
      · rw [e1, e2, hP0] at key
        refine le_trans key (mul_le_mul_of_nonneg_left ?_ hC5.le)
        have hd0 : (0 : ℝ) ≤ (m : ℝ) - ((A₀ + 1 : ℕ) : ℝ) := by
          have : ((A₀ + 1 : ℕ) : ℝ) ≤ m := by exact_mod_cast hlt.le
          linarith
        have hdM : (m : ℝ) - ((A₀ + 1 : ℕ) : ℝ) ≤ M := by
          have : (0 : ℝ) ≤ ((A₀ + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
          linarith
        have := Real.rpow_le_rpow hd0 hdM (by norm_num : (0 : ℝ) ≤ 7 / 8)
        gcongr
      · intro j hj x hx
        have hx1 : (A₀ : ℝ) + 1 ≤ x := by
          have := hx.1
          push_cast at this
          exact this
        exact hPd j hj x (hrange x hx1 (le_trans hx.2 hm2')).1
      · intro x hx
        have hx1 : (A₀ : ℝ) + 1 ≤ x := by
          have := hx.1
          push_cast at this
          exact this
        obtain ⟨hxpos, -, hxlo, hxhi⟩ := hrange x hx1 (le_trans hx.2 hm2')
        have hhx : (h : ℝ) * x ≤ t / 2000 :=
          le_trans (mul_le_mul_of_nonneg_left hxhi.le hh'.le) (h_mul_M_le t ht h N hh hN)
        obtain ⟨hlo, hhi⟩ := hP5 x hxpos hhx
        have hs : 0 ≤ Real.sqrt (t * h) := Real.sqrt_nonneg _
        rw [one_mul]
        constructor
        · refine le_trans ?_ hlo
          have := Real.rpow_le_rpow_of_nonpos hxpos hxhi.le
            (by norm_num : (-(9 / 2 : ℝ)) ≤ 0)
          exact mul_le_mul_of_nonneg_left this (by positivity)
        · refine le_trans hhi ?_
          rw [← ratio_lam c₁ c₂ _ M hc₁ hM]
          have := Real.rpow_le_rpow_of_nonpos (by positivity : 0 < M / 26) hxlo
            (by norm_num : (-(9 / 2 : ℝ)) ≤ 0)
          have hc₂ : 0 ≤ c₂ := by
            have h0 : 0 < c₁ * Real.sqrt (t * h) * x ^ (-(9 / 2 : ℝ)) := by positivity
            have h1 : 0 < c₂ * (Real.sqrt (t * h) * x ^ (-(9 / 2 : ℝ))) := by
              rw [← mul_assoc]; exact lt_of_lt_of_le h0 (le_trans hlo hhi)
            have h2 : 0 < Real.sqrt (t * h) * x ^ (-(9 / 2 : ℝ)) := by positivity
            exact (pos_of_mul_pos_left h1 h2.le).le
          exact mul_le_mul_of_nonneg_left this (by positivity)

/-! ## The stub -/
theorem shifted_sum_bound :
    ∃ C t₀ : ℝ, 0 < C ∧ 2 ≤ t₀ ∧ ∀ t : ℝ, t₀ ≤ t → ∀ N N' h : ℕ, 1 ≤ h → 100 * h ≤ N →
      (N : ℝ) ^ 2 ≤ t → N < N' → N' ≤ 2 * N →
      ‖∑ n ∈ Finset.Ioc N N', e (phi t h n)‖ ≤
        C * ((N : ℝ) ^ (-(1 / 5 : ℝ)) * (t * h) ^ (11 / 30 : ℝ) +
          (N : ℝ) ^ (-(11 / 20 : ℝ)) * (t * h) ^ (61 / 120 : ℝ) +
          (N : ℝ) ^ (3 / 2 : ℝ) * (t * h) ^ (-(1 / 2 : ℝ)) + Real.log t +
          (t * h) ^ (2 / 5 : ℝ) * (N : ℝ) ^ (-(2 / 5 : ℝ))) := by
  obtain ⟨κ, Cb, hCb, hb⟩ := GuthMaynard.SubWeyl.b_process 10 (by norm_num)
  obtain ⟨c₁, c₂, hc₁, hc₁₂, hP⟩ := GuthMaynard.SubWeyl.dualPhase_derivs
  have hR : (1 : ℝ) ≤ c₂ / c₁ * (26 : ℝ) ^ (9 / 2 : ℝ) := by
    have h1 : 1 ≤ c₂ / c₁ := (one_le_div hc₁).mpr hc₁₂
    have h2 : (1 : ℝ) ≤ (26 : ℝ) ^ (9 / 2 : ℝ) := Real.one_le_rpow (by norm_num) (by norm_num)
    calc (1 : ℝ) = 1 * 1 := by ring
      _ ≤ c₂ / c₁ * (26 : ℝ) ^ (9 / 2 : ℝ) := mul_le_mul h1 h2 zero_le_one (by linarith)
  obtain ⟨C5, hC5, h5⟩ := GuthMaynard.SubWeyl.kth_derivative_test 5 (by norm_num) _ hR
  have hp : 0 < c₁ ^ (1 / 30 : ℝ) := Real.rpow_pos_of_pos hc₁ _
  have hq : 0 < c₁ ^ (-(1 / 30 : ℝ)) := Real.rpow_pos_of_pos hc₁ _
  have hκ : 0 ≤ ‖κ‖ := norm_nonneg κ
  set k1 : ℝ := ‖κ‖ * (12 * C5 * c₁ ^ (1 / 30 : ℝ)) with hk1
  set k2 : ℝ := ‖κ‖ * (12 * C5 * c₁ ^ (-(1 / 30 : ℝ))) with hk2
  have hk1n : 0 ≤ k1 := by positivity
  have hk2n : 0 ≤ k2 := by positivity
  refine ⟨k1 + k2 + 12 * ‖κ‖ + 8 * Cb, 2, by positivity, le_rfl, ?_⟩
  intro t ht N N' h hh hN hNt hNN' hN'2
  have ht0 : 0 < t := by linarith
  have hNpos : 0 < N := by omega
  have hN'pos : 0 < N' := by omega
  have hh' : (1 : ℝ) ≤ h := by exact_mod_cast hh
  have hNh : (100 : ℝ) * h ≤ N := by exact_mod_cast hN
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hNpos
  have hNr0 : (0 : ℝ) < N := by linarith
  have hN2r : (N' : ℝ) ≤ 2 * N := by exact_mod_cast hN'2
  have hNN'r : (N : ℝ) < N' := by exact_mod_cast hNN'
  have hT : 0 < t * h := by positivity
  obtain ⟨P, hP0, hPd, hP5⟩ := hP t h ht0 hh
  have hdual := dual_sum_bound c₁ c₂ C5 hc₁ hC5 h5 t ht0 h N N' hh hN hNN' hN'2 P hP0 hPd hP5
  have hlam2 : 0 < t * h / (26 * (N : ℝ) ^ 3) := by positivity
  have hlam3 : 0 < t * h / (N : ℝ) ^ 4 := by positivity
  have hbp := hb (phi t h) (phi1 t h) (phi2 t h) (phi3 t h) (fun ν : ℤ => xst t h (-(ν : ℝ)))
    N N' (t * h / (26 * (N : ℝ) ^ 3)) (t * h / (N : ℝ) ^ 4) hNN' hlam2 hlam3
    (fun x hx => (GuthMaynard.SubWeyl.phi_hasDerivAt t h x (lt_of_lt_of_le hNr0 hx.1)).1)
    (fun x hx => (GuthMaynard.SubWeyl.phi_hasDerivAt t h x (lt_of_lt_of_le hNr0 hx.1)).2.1)
    (fun x hx => (GuthMaynard.SubWeyl.phi_hasDerivAt t h x (lt_of_lt_of_le hNr0 hx.1)).2.2)
    (fun x hx => by
      have := GuthMaynard.SubWeyl.phi_bounds t ht0 h N hh hN x hx.1 (le_trans hx.2 hN2r)
      exact ⟨this.1, this.2.1⟩)
    (fun x hx => by
      have := GuthMaynard.SubWeyl.phi_bounds t ht0 h N hh hN x hx.1 (le_trans hx.2 hN2r)
      exact le_trans this.2.2 (by linarith))
    (fun ν h1 h2 => by
      obtain ⟨hμ, hmem⟩ := xst_mem t ht0 h hh N N' hNpos hN'pos (-(ν : ℝ))
        (by simpa using h1) (by simpa using h2)
      refine ⟨hmem, ?_⟩
      have := (GuthMaynard.SubWeyl.xst_spec t ht0 h hh _ hμ).2.1
      simpa using this)
  -- the five terms
  set X1 : ℝ := (N : ℝ) ^ (-(1 / 5 : ℝ)) * (t * h) ^ (11 / 30 : ℝ) with hX1
  set X2 : ℝ := (N : ℝ) ^ (-(11 / 20 : ℝ)) * (t * h) ^ (61 / 120 : ℝ) with hX2
  set X3 : ℝ := (N : ℝ) ^ (3 / 2 : ℝ) * (t * h) ^ (-(1 / 2 : ℝ)) with hX3
  set X5 : ℝ := (t * h) ^ (2 / 5 : ℝ) * (N : ℝ) ^ (-(2 / 5 : ℝ)) with hX5
  have hX1n : 0 ≤ X1 := by positivity
  have hX2n : 0 ≤ X2 := by positivity
  have hX3n : 0 ≤ X3 := by positivity
  have hX5n : 0 ≤ X5 := by positivity
  have hX4n : 0 ≤ Real.log t := Real.log_nonneg (by linarith)
  have hA := mono3 (t * h) N hT hNr0
  have hm1 := mono1 (t * h) N c₁ hT hNr0 hc₁
  have hm2 := mono2 (t * h) N c₁ hT hNr0 hc₁
  rw [← hX3] at hA hm1 hm2
  rw [← hX1] at hm1
  rw [← hX2] at hm2
  -- the dual sum
  set Y1 : ℝ := t * h / (N : ℝ) ^ 2 *
    (c₁ * Real.sqrt (t * h) * (t * h / (N : ℝ) ^ 2) ^ (-(9 / 2 : ℝ))) ^ (1 / 30 : ℝ) with hY1
  set Y2 : ℝ := (t * h / (N : ℝ) ^ 2) ^ (7 / 8 : ℝ) *
    (c₁ * Real.sqrt (t * h) * (t * h / (N : ℝ) ^ 2) ^ (-(9 / 2 : ℝ))) ^ (-(1 / 30 : ℝ)) with hY2
  have hY1n : 0 ≤ Y1 := by positivity
  have hY2n : 0 ≤ Y2 := by positivity
  set D : ℂ := ∑ ν ∈ Finset.Ioc ⌊phi1 t h N⌋ ⌊phi1 t h N'⌋,
        ((phi2 t h (xst t h (-(ν : ℝ))) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
          e (phi t h (xst t h (-(ν : ℝ))) - (ν : ℝ) * xst t h (-(ν : ℝ))) with hD
  have hD1 : ‖D‖ ≤ 12 * X3 + 12 * C5 * c₁ ^ (1 / 30 : ℝ) * X1 +
      12 * C5 * c₁ ^ (-(1 / 30 : ℝ)) * X2 := by
    have h0 : (0 : ℝ) ≤ 1 + C5 * (Y1 + Y2) := by positivity
    calc ‖D‖ ≤ 2 * (t * h / (26 * (N : ℝ) ^ 3)) ^ (-(1 / 2 : ℝ)) * (1 + C5 * (Y1 + Y2)) := hdual
      _ ≤ 2 * (6 * X3) * (1 + C5 * (Y1 + Y2)) := by gcongr
      _ = 12 * X3 + 12 * C5 * (X3 * Y1) + 12 * C5 * (X3 * Y2) := by ring
      _ = _ := by rw [hm1, hm2]; ring
  -- the error terms
  have hE2 : Real.log (2 + ((N' : ℝ) - N) * (t * h / (26 * (N : ℝ) ^ 3))) ≤ 2 * Real.log t := by
    refine log_term t (t * h) N _ ht hNr ?_ hT (by linarith) (by linarith)
    have hsq : (N : ℝ) * 1 ≤ (N : ℝ) * N := mul_le_mul_of_nonneg_left hNr hNr0.le
    have : (h : ℝ) ≤ t := by rw [sq] at hNt; linarith
    exact mul_le_mul_of_nonneg_left this ht0.le
  have hE3 : ((N' : ℝ) - N) * (t * h / (26 * (N : ℝ) ^ 3)) ^ (1 / 5 : ℝ) *
      (t * h / (N : ℝ) ^ 4) ^ (1 / 5 : ℝ) ≤ X5 := by
    refine le_trans ?_ (mono4 (t * h) N hT hNr0)
    have : (N' : ℝ) - N ≤ N := by linarith
    gcongr
  have hS : ‖∑ n ∈ Finset.Ioc N N', e (phi t h n)‖ ≤
      ‖κ‖ * ‖D‖ + Cb * (6 * X3 + 2 * Real.log t + X5) := by
    have h1 : ∑ n ∈ Finset.Ioc N N', e (phi t h n) =
        (∑ n ∈ Finset.Ioc N N', e (phi t h n) - κ * D) + κ * D := by ring
    rw [h1]
    refine le_trans (norm_add_le _ _) ?_
    rw [norm_mul, add_comm]
    refine add_le_add le_rfl (le_trans hbp (mul_le_mul_of_nonneg_left ?_ hCb.le))
    exact add_le_add (add_le_add hA hE2) hE3
  have hS2 : ‖κ‖ * ‖D‖ ≤ ‖κ‖ * (12 * X3 + 12 * C5 * c₁ ^ (1 / 30 : ℝ) * X1 +
      12 * C5 * c₁ ^ (-(1 / 30 : ℝ)) * X2) := mul_le_mul_of_nonneg_left hD1 hκ
  refine le_trans hS ?_
  have g1 := mul_nonneg (by positivity : 0 ≤ k2 + 12 * ‖κ‖ + 8 * Cb) hX1n
  have g2 := mul_nonneg (by positivity : 0 ≤ k1 + 12 * ‖κ‖ + 8 * Cb) hX2n
  have g3 := mul_nonneg (by positivity : 0 ≤ k1 + k2 + 2 * Cb) hX3n
  have g4 := mul_nonneg (by positivity : 0 ≤ k1 + k2 + 12 * ‖κ‖ + 6 * Cb) hX4n
  have g5 := mul_nonneg (by positivity : 0 ≤ k1 + k2 + 12 * ‖κ‖ + 7 * Cb) hX5n
  have hk1' : ‖κ‖ * (12 * C5 * c₁ ^ (1 / 30 : ℝ) * X1) = k1 * X1 := by rw [hk1]; ring
  have hk2' : ‖κ‖ * (12 * C5 * c₁ ^ (-(1 / 30 : ℝ)) * X2) = k2 * X2 := by rw [hk2]; ring
  rw [mul_add, mul_add, hk1', hk2'] at hS2
  linarith [hS2, g1, g2, g3, g4, g5]

end GuthMaynard.SubWeyl.PartS
end

section
namespace GuthMaynard.SubWeyl
/-! ## Part S: the shifted sums -/
alias shifted_sum_bound := GuthMaynard.SubWeyl.PartS.shifted_sum_bound

end GuthMaynard.SubWeyl
end

section
namespace GuthMaynard.SubWeyl.PartL
/-!
# Part L: blocks with `t^{43/100} ≤ N ≤ t^{1/2}` (A-process and exponent bookkeeping)
-/
lemma natCast_cpow_eq_e (t : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    (n : ℂ) ^ ((t : ℂ) * Complex.I) = e (t / (2 * Real.pi) * Real.log n) := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hlog : Complex.log (n : ℂ) = ((Real.log n : ℝ) : ℂ) := by
    rw [Complex.ofReal_log (Nat.cast_nonneg n)]
    simp
  have h2 : 2 * Real.pi * (t / (2 * Real.pi) * Real.log n) = t * Real.log n := by
    field_simp
  rw [Complex.cpow_def_of_ne_zero hn0, e, hlog, h2]
  congr 1
  push_cast
  ring

lemma e_mul_conj (x y : ℝ) : e x * (starRingEnd ℂ) (e y) = e (x - y) := by
  unfold e
  rw [← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  rw [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

lemma shifted_term (t : ℝ) (n h : ℕ) (hn : 1 ≤ n) :
    ((n + h : ℕ) : ℂ) ^ ((t : ℂ) * Complex.I) *
      (starRingEnd ℂ) ((n : ℂ) ^ ((t : ℂ) * Complex.I)) = e (phi t h n) := by
  rw [natCast_cpow_eq_e t (n + h) (by omega), natCast_cpow_eq_e t n hn, e_mul_conj]
  congr 1
  unfold phi
  push_cast
  ring

lemma norm_term (t : ℝ) (n : ℕ) (hn : 1 ≤ n) : ‖(n : ℂ) ^ ((t : ℂ) * Complex.I)‖ = 1 := by
  rw [Complex.norm_natCast_cpow_of_pos (by omega)]
  simp

/-- Comparing positive reals through logarithms. -/
lemma le_of_log_le {X Y : ℝ} (hX : 0 < X) (hY : 0 < Y) (h : Real.log X ≤ Real.log Y) : X ≤ Y :=
  (Real.log_le_log_iff hX hY).mp h

/-- The basic logarithmic facts in the range `t^{43/100} ≤ N ≤ t^{1/2}`, `t ≥ 10^8`. -/
lemma log_facts (t N : ℝ) (ht : (10 : ℝ) ^ 8 ≤ t) (hN : t ^ (43 / 100 : ℝ) ≤ N)
    (hNt : N ^ 2 ≤ t) :
    0 < t ∧ 0 < N ∧ 43 / 100 * Real.log t ≤ Real.log N ∧ 2 * Real.log N ≤ Real.log t ∧
      8 * Real.log 10 ≤ Real.log t ∧ 3 * Real.log 2 ≤ Real.log 10 ∧ 0 < Real.log 2 ∧
      Real.log (N ^ (36 / 41 : ℝ) * t ^ (-(11 / 41 : ℝ))) =
        36 / 41 * Real.log N - 11 / 41 * Real.log t := by
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht
  have hN0 : 0 < N := lt_of_lt_of_le (by positivity) hN
  refine ⟨ht0, hN0, ?_, ?_, ?_, ?_, Real.log_pos (by norm_num), ?_⟩
  · have := Real.log_le_log (by positivity) hN
    rwa [Real.log_rpow ht0] at this
  · have := Real.log_le_log (by positivity) hNt
    rwa [Real.log_pow] at this
  · have := Real.log_le_log (by norm_num) ht
    rwa [Real.log_pow] at this
  · have h8 : Real.log ((2 : ℝ) ^ 3) ≤ Real.log 10 := Real.log_le_log (by norm_num) (by norm_num)
    rwa [Real.log_pow] at h8
  · rw [Real.log_mul (by positivity) (by positivity), Real.log_rpow hN0, Real.log_rpow ht0]
    ring

/-- Size of `X = N^{36/41} t^{-11/41}`. -/
lemma X_facts (t N : ℝ) (ht : (10 : ℝ) ^ 8 ≤ t) (hN : t ^ (43 / 100 : ℝ) ≤ N)
    (hNt : N ^ 2 ≤ t) :
    2 ≤ N ^ (36 / 41 : ℝ) * t ^ (-(11 / 41 : ℝ)) ∧
      100 * (N ^ (36 / 41 : ℝ) * t ^ (-(11 / 41 : ℝ))) ≤ N ∧
      N ^ (36 / 41 : ℝ) * t ^ (-(11 / 41 : ℝ)) ≤ Real.sqrt N * t ^ (27 / 164 : ℝ) := by
  obtain ⟨ht0, hN0, hv1, hv2, hu8, h10, h2, hlogX⟩ := log_facts t N ht hN hNt
  have hX : 0 < N ^ (36 / 41 : ℝ) * t ^ (-(11 / 41 : ℝ)) := by positivity
  have h100 : Real.log 100 = 2 * Real.log 10 := by
    rw [show (100 : ℝ) = 10 ^ 2 by norm_num, Real.log_pow]
    push_cast
    ring
  refine ⟨?_, ?_, ?_⟩
  · refine le_of_log_le (by norm_num) hX ?_
    rw [hlogX]
    linarith
  · refine le_of_log_le (by positivity) hN0 ?_
    rw [Real.log_mul (by norm_num) hX.ne', hlogX, h100]
    linarith
  · refine le_of_log_le hX (by positivity) ?_
    rw [hlogX, Real.log_mul (by positivity) (by positivity), Real.log_sqrt hN0.le,
      Real.log_rpow ht0]
    linarith

/-- The monomial bookkeeping for `X/2 ≤ H ≤ X`. -/
lemma large_arith (t N Hr : ℝ) (ht : (10 : ℝ) ^ 8 ≤ t) (hN : t ^ (43 / 100 : ℝ) ≤ N)
    (hNt : N ^ 2 ≤ t) (hH1 : N ^ (36 / 41 : ℝ) * t ^ (-(11 / 41 : ℝ)) / 2 ≤ Hr)
    (hH2 : Hr ≤ N ^ (36 / 41 : ℝ) * t ^ (-(11 / 41 : ℝ))) :
    N ^ 2 / Hr ≤ 2 * (N * t ^ (27 / 82 : ℝ)) ∧
      N ^ (-(1 / 5 : ℝ)) * (t * Hr) ^ (11 / 30 : ℝ) ≤ t ^ (27 / 82 : ℝ) ∧
      N ^ (-(11 / 20 : ℝ)) * (t * Hr) ^ (61 / 120 : ℝ) ≤ t ^ (27 / 82 : ℝ) ∧
      N ^ (3 / 2 : ℝ) * t ^ (-(1 / 2 : ℝ)) ≤ t ^ (27 / 82 : ℝ) ∧
      (t * Hr) ^ (2 / 5 : ℝ) * N ^ (-(2 / 5 : ℝ)) ≤ t ^ (27 / 82 : ℝ) := by
  obtain ⟨ht0, hN0, hv1, hv2, hu8, h10, h2, hlogX⟩ := log_facts t N ht hN hNt
  have hX : 0 < N ^ (36 / 41 : ℝ) * t ^ (-(11 / 41 : ℝ)) := by positivity
  have hHr : 0 < Hr := lt_of_lt_of_le (by positivity) hH1
  have hh2 : Real.log Hr ≤ 36 / 41 * Real.log N - 11 / 41 * Real.log t := by
    rw [← hlogX]
    exact Real.log_le_log hHr hH2
  have hh1 : 36 / 41 * Real.log N - 11 / 41 * Real.log t - Real.log 2 ≤ Real.log Hr := by
    have := Real.log_le_log (by positivity) hH1
    rwa [Real.log_div hX.ne' (by norm_num), hlogX] at this
  have htH : 0 < t * Hr := by positivity
  have hlogtH : Real.log (t * Hr) = Real.log t + Real.log Hr := Real.log_mul ht0.ne' hHr.ne'
  have hT : 0 < t ^ (27 / 82 : ℝ) := by positivity
  have hlogT : Real.log (t ^ (27 / 82 : ℝ)) = 27 / 82 * Real.log t := Real.log_rpow ht0 _
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · refine le_of_log_le (by positivity) (by positivity) ?_
    rw [Real.log_div (by positivity) hHr.ne', Real.log_pow, Real.log_mul (by norm_num)
      (by positivity), Real.log_mul hN0.ne' hT.ne', hlogT]
    push_cast
    linarith
  · refine le_of_log_le (by positivity) hT ?_
    rw [hlogT, Real.log_mul (by positivity) (by positivity), Real.log_rpow hN0,
      Real.log_rpow htH, hlogtH]
    linarith
  · refine le_of_log_le (by positivity) hT ?_
    rw [hlogT, Real.log_mul (by positivity) (by positivity), Real.log_rpow hN0,
      Real.log_rpow htH, hlogtH]
    linarith
  · refine le_of_log_le (by positivity) hT ?_
    rw [hlogT, Real.log_mul (by positivity) (by positivity), Real.log_rpow hN0,
      Real.log_rpow ht0]
    linarith
  · refine le_of_log_le (by positivity) hT ?_
    rw [hlogT, Real.log_mul (by positivity) (by positivity), Real.log_rpow hN0,
      Real.log_rpow htH, hlogtH]
    linarith

/-- Each shifted-sum bound, uniformly in `1 ≤ h ≤ H`. -/
lemma shifted_uniform (t N Hr hr : ℝ) (ht : (10 : ℝ) ^ 8 ≤ t) (hN : t ^ (43 / 100 : ℝ) ≤ N)
    (hNt : N ^ 2 ≤ t) (hH1 : N ^ (36 / 41 : ℝ) * t ^ (-(11 / 41 : ℝ)) / 2 ≤ Hr)
    (hH2 : Hr ≤ N ^ (36 / 41 : ℝ) * t ^ (-(11 / 41 : ℝ))) (hh1 : 1 ≤ hr) (hhH : hr ≤ Hr) :
    N ^ (-(1 / 5 : ℝ)) * (t * hr) ^ (11 / 30 : ℝ) +
        N ^ (-(11 / 20 : ℝ)) * (t * hr) ^ (61 / 120 : ℝ) +
        N ^ (3 / 2 : ℝ) * (t * hr) ^ (-(1 / 2 : ℝ)) + Real.log t +
        (t * hr) ^ (2 / 5 : ℝ) * N ^ (-(2 / 5 : ℝ)) ≤ 8 * t ^ (27 / 82 : ℝ) := by
  obtain ⟨hb, hc, hd, he⟩ := (large_arith t N Hr ht hN hNt hH1 hH2).2
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht
  have hN0 : 0 < N := lt_of_lt_of_le (by positivity) hN
  have hth0 : 0 ≤ t * hr := by positivity
  have hthH : t * hr ≤ t * Hr := mul_le_mul_of_nonneg_left hhH ht0.le
  have hlog : Real.log t ≤ 4 * t ^ (27 / 82 : ℝ) := by
    have h := Real.log_le_rpow_div ht0.le (by norm_num : (0 : ℝ) < 27 / 82)
    have hT : 0 ≤ t ^ (27 / 82 : ℝ) := by positivity
    calc Real.log t ≤ t ^ (27 / 82 : ℝ) / (27 / 82) := h
      _ ≤ 4 * t ^ (27 / 82 : ℝ) := by linarith
  have h1 : N ^ (-(1 / 5 : ℝ)) * (t * hr) ^ (11 / 30 : ℝ) ≤ t ^ (27 / 82 : ℝ) :=
    le_trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hth0 hthH (by norm_num))
      (by positivity)) hb
  have h2 : N ^ (-(11 / 20 : ℝ)) * (t * hr) ^ (61 / 120 : ℝ) ≤ t ^ (27 / 82 : ℝ) :=
    le_trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hth0 hthH (by norm_num))
      (by positivity)) hc
  have h3 : N ^ (3 / 2 : ℝ) * (t * hr) ^ (-(1 / 2 : ℝ)) ≤ t ^ (27 / 82 : ℝ) := by
    refine le_trans (mul_le_mul_of_nonneg_left ?_ (by positivity)) hd
    exact Real.rpow_le_rpow_of_nonpos ht0 (by nlinarith) (by norm_num)
  have h4 : (t * hr) ^ (2 / 5 : ℝ) * N ^ (-(2 / 5 : ℝ)) ≤ t ^ (27 / 82 : ℝ) :=
    le_trans (mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hth0 hthH (by norm_num))
      (by positivity)) he
  linarith

theorem block_bound_large :
    ∃ C t₀ : ℝ, 0 < C ∧ ∀ t : ℝ, t₀ ≤ t → ∀ N N' : ℕ, t ^ (43 / 100 : ℝ) ≤ N →
      (N : ℝ) ^ 2 ≤ t → N < N' → N' ≤ 2 * N →
      ‖∑ n ∈ Finset.Ioc N N', (n : ℂ) ^ ((t : ℂ) * Complex.I)‖ ≤
        C * Real.sqrt N * t ^ (27 / 164 : ℝ) := by
  obtain ⟨C₁, t₁, hC₁, _, hS⟩ := GuthMaynard.SubWeyl.shifted_sum_bound
  refine ⟨4 + 32 * C₁, max t₁ ((10 : ℝ) ^ 8), by positivity,
    fun t ht N N' hN hNt hNN' hN'2 => ?_⟩
  have ht1 : t₁ ≤ t := le_trans (le_max_left _ _) ht
  have ht8 : (10 : ℝ) ^ 8 ≤ t := le_trans (le_max_right _ _) ht
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht8
  have hN0 : (0 : ℝ) < N := lt_of_lt_of_le (by positivity) hN
  have hN1 : 1 ≤ N := by
    have : 0 < N := by exact_mod_cast hN0
    omega
  have hNN'r : (N : ℝ) < N' := by exact_mod_cast hNN'
  have hN'2r : (N' : ℝ) ≤ 2 * N := by exact_mod_cast hN'2
  set X : ℝ := (N : ℝ) ^ (36 / 41 : ℝ) * t ^ (-(11 / 41 : ℝ)) with hX
  obtain ⟨hX2, hX100, hXtriv⟩ := X_facts t N ht8 hN hNt
  rw [← hX] at hX2 hX100 hXtriv
  set H : ℕ := ⌊X⌋₊ with hH
  have hHle : (H : ℝ) ≤ X := Nat.floor_le (by linarith)
  have hHgt : X < (H : ℝ) + 1 := Nat.lt_floor_add_one X
  have hHhalf : X / 2 ≤ (H : ℝ) := by linarith
  have hHpos : (0 : ℝ) < H := by linarith
  have hH1 : 1 ≤ H := by
    have : 0 < H := by exact_mod_cast hHpos
    omega
  have hH100 : 100 * H ≤ N := by
    have : ((100 * H : ℕ) : ℝ) ≤ N := by
      push_cast
      linarith
    exact_mod_cast this
  set Y : ℝ := Real.sqrt N * t ^ (27 / 164 : ℝ) with hY
  have hYnn : 0 ≤ Y := by positivity
  have hK1 : (1 : ℝ) ≤ 4 + 32 * C₁ := by linarith
  rw [mul_assoc]
  by_cases hcase : N' - N < H
  · -- short block: trivial bound
    have hcard : ‖∑ n ∈ Finset.Ioc N N', (n : ℂ) ^ ((t : ℂ) * Complex.I)‖ ≤ ((N' - N : ℕ) : ℝ) := by
      calc ‖∑ n ∈ Finset.Ioc N N', (n : ℂ) ^ ((t : ℂ) * Complex.I)‖
          ≤ ∑ n ∈ Finset.Ioc N N', ‖(n : ℂ) ^ ((t : ℂ) * Complex.I)‖ := norm_sum_le _ _
        _ = ∑ n ∈ Finset.Ioc N N', (1 : ℝ) :=
            Finset.sum_congr rfl fun n hn =>
              norm_term t n (by rw [Finset.mem_Ioc] at hn; omega)
        _ = ((N' - N : ℕ) : ℝ) := by simp
    have hlt : ((N' - N : ℕ) : ℝ) ≤ H := by exact_mod_cast hcase.le
    calc _ ≤ Y := by linarith
      _ ≤ (4 + 32 * C₁) * Y := le_mul_of_one_le_left hYnn hK1
  · -- A-process
    have hHab : H ≤ N' - N := by omega
    set z : ℕ → ℂ := fun n => (n : ℂ) ^ ((t : ℂ) * Complex.I) with hz
    have hW := GuthMaynard.SubWeyl.weyl_differencing z N N' H hH1 hHab
    have hz2 : ∑ n ∈ Finset.Ioc N N', ‖z n‖ ^ 2 = (N' : ℝ) - N := by
      have : ∑ n ∈ Finset.Ioc N N', ‖z n‖ ^ 2 = ∑ n ∈ Finset.Ioc N N', (1 : ℝ) :=
        Finset.sum_congr rfl fun n hn => by
          rw [hz, norm_term t n (by rw [Finset.mem_Ioc] at hn; omega)]
          norm_num
      rw [this]
      simp [Nat.cast_sub hNN'.le]
    set T : ℝ := t ^ (27 / 82 : ℝ) with hT
    have hTnn : 0 ≤ T := by positivity
    have hcorr : ∀ h ∈ Finset.Ico 1 H,
        ‖∑ n ∈ Finset.Ioc N (N' - h), z (n + h) * (starRingEnd ℂ) (z n)‖ ≤ C₁ * (8 * T) := by
      intro h hh
      rw [Finset.mem_Ico] at hh
      have hsum : ∑ n ∈ Finset.Ioc N (N' - h), z (n + h) * (starRingEnd ℂ) (z n) =
          ∑ n ∈ Finset.Ioc N (N' - h), e (phi t h n) :=
        Finset.sum_congr rfl fun n hn => by
          rw [Finset.mem_Ioc] at hn
          exact shifted_term t n h (by omega)
      rw [hsum]
      have hb := hS t ht1 N (N' - h) h hh.1 (by omega) hNt (by omega) (by omega)
      have hhr1 : (1 : ℝ) ≤ h := by exact_mod_cast hh.1
      have hhrH : (h : ℝ) ≤ H := by exact_mod_cast hh.2.le
      exact le_trans hb (mul_le_mul_of_nonneg_left
        (shifted_uniform t N H h ht8 hN hNt hHhalf hHle hhr1 hhrH) hC₁.le)
    have hsumh : ∑ h ∈ Finset.Ico 1 H,
        ‖∑ n ∈ Finset.Ioc N (N' - h), z (n + h) * (starRingEnd ℂ) (z n)‖ ≤
          H * (C₁ * (8 * T)) := by
      calc _ ≤ ∑ _h ∈ Finset.Ico 1 H, C₁ * (8 * T) := Finset.sum_le_sum hcorr
        _ = ((H - 1 : ℕ) : ℝ) * (C₁ * (8 * T)) := by simp
        _ ≤ H * (C₁ * (8 * T)) := by
            refine mul_le_mul_of_nonneg_right ?_ (by positivity)
            exact_mod_cast Nat.sub_le H 1
    have ha := (large_arith t N H ht8 hN hNt hHhalf hHle).1
    have hsq : ‖∑ n ∈ Finset.Ioc N N', z n‖ ^ 2 ≤ (4 + 32 * C₁) * (N * T) := by
      rw [hz2] at hW
      have hL0 : 0 ≤ (N' : ℝ) - N := by linarith
      have hLN : (N' : ℝ) - N ≤ N := by linarith
      calc ‖∑ n ∈ Finset.Ioc N N', z n‖ ^ 2
          ≤ 2 * ((N' : ℝ) - N) / H * ((N' : ℝ) - N + 2 * ∑ h ∈ Finset.Ico 1 H,
              ‖∑ n ∈ Finset.Ioc N (N' - h), z (n + h) * (starRingEnd ℂ) (z n)‖) := hW
        _ ≤ 2 * (N : ℝ) / H * ((N : ℝ) + 2 * (H * (C₁ * (8 * T)))) := by
            refine mul_le_mul ?_ (by linarith) ?_ (by positivity)
            · exact div_le_div_of_nonneg_right (by linarith) hHpos.le
            · exact add_nonneg hL0 (mul_nonneg (by norm_num)
                (Finset.sum_nonneg fun h _ => norm_nonneg _))
        _ = 2 * ((N : ℝ) ^ 2 / H) + 32 * C₁ * (N * T) := by
            field_simp
            ring
        _ ≤ 2 * (2 * (N * T)) + 32 * C₁ * (N * T) := by linarith
        _ = (4 + 32 * C₁) * (N * T) := by ring
    have hTsq : T = t ^ (27 / 164 : ℝ) * t ^ (27 / 164 : ℝ) := by
      rw [hT, ← Real.rpow_add ht0]
      norm_num
    have hYsq : Y ^ 2 = N * T := by
      rw [hY, mul_pow, Real.sq_sqrt hN0.le, hTsq]
      ring
    refine le_of_pow_le_pow_left₀ (two_ne_zero) (by positivity) ?_
    calc ‖∑ n ∈ Finset.Ioc N N', z n‖ ^ 2 ≤ (4 + 32 * C₁) * (N * T) := hsq
      _ ≤ (4 + 32 * C₁) * ((4 + 32 * C₁) * (N * T)) :=
          le_mul_of_one_le_left (by positivity) hK1
      _ = ((4 + 32 * C₁) * Y) ^ 2 := by
          rw [mul_pow, hYsq]
          ring

end GuthMaynard.SubWeyl.PartL
end

section
namespace GuthMaynard.SubWeyl
/-! ## Part L: blocks with `t^{43/100} ≤ N ≤ t^{1/2}` -/
alias block_bound_large := GuthMaynard.SubWeyl.PartL.block_bound_large

end GuthMaynard.SubWeyl
end

section
namespace GuthMaynard.SubWeyl.PartM
/-!
# Part M: blocks with `N ≤ t^{43/100}` (fourth-derivative test)
-/
lemma natCast_cpow_eq_e (t : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    (n : ℂ) ^ ((t : ℂ) * Complex.I) = e (t / (2 * Real.pi) * Real.log n) := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hlog : Complex.log (n : ℂ) = ((Real.log n : ℝ) : ℂ) := by
    rw [Complex.ofReal_log (Nat.cast_nonneg n)]
    simp
  have h2 : 2 * Real.pi * (t / (2 * Real.pi) * Real.log n) = t * Real.log n := by
    field_simp
  rw [Complex.cpow_def_of_ne_zero hn0, e, hlog, h2]
  congr 1
  push_cast
  ring

/-- The phase `c log x` and its derivatives up to order four. -/
noncomputable def Fm (c : ℝ) : ℕ → ℝ → ℝ
  | 0 => fun x => c * Real.log x
  | 1 => fun x => c * x⁻¹
  | 2 => fun x => -c * (x ^ 2)⁻¹
  | 3 => fun x => 2 * c * (x ^ 3)⁻¹
  | _ => fun x => -6 * c * (x ^ 4)⁻¹

lemma Fm_deriv (c x : ℝ) (hx : x ≠ 0) (j : ℕ) (hj : j < 4) :
    HasDerivAt (Fm c j) (Fm c (j + 1) x) x := by
  interval_cases j
  · exact (Real.hasDerivAt_log hx).const_mul c
  · refine ((hasDerivAt_inv hx).const_mul c).congr_deriv ?_
    show c * -(x ^ 2)⁻¹ = -c * (x ^ 2)⁻¹
    ring
  · have h := ((hasDerivAt_pow 2 x).inv (pow_ne_zero 2 hx)).const_mul (-c)
    refine h.congr_deriv ?_
    show _ = 2 * c * (x ^ 3)⁻¹
    field_simp
    ring
  · have h := ((hasDerivAt_pow 3 x).inv (pow_ne_zero 3 hx)).const_mul (2 * c)
    refine h.congr_deriv ?_
    show _ = -6 * c * (x ^ 4)⁻¹
    field_simp
    ring

/-- Comparing positive reals through logarithms. -/
lemma le_of_log_le {X Y : ℝ} (hX : 0 < X) (hY : 0 < Y) (h : Real.log X ≤ Real.log Y) : X ≤ Y :=
  (Real.log_le_log_iff hX hY).mp h

/-- The two terms of the fourth-derivative test are `≪ √N t^{27/164}` for `N ≤ t^{43/100}`. -/
lemma mid_arith (t N L : ℝ) (ht : 1 ≤ t) (hN : 1 ≤ N) (hNt : N ≤ t ^ (43 / 100 : ℝ))
    (hL : 0 < L) (hLN : L ≤ N) :
    L * (t / (32 * N ^ 4)) ^ (1 / 14 : ℝ) ≤ Real.sqrt N * t ^ (27 / 164 : ℝ) ∧
      L ^ (3 / 4 : ℝ) * (t / (32 * N ^ 4)) ^ (-(1 / 14 : ℝ)) ≤
        32 * (Real.sqrt N * t ^ (27 / 164 : ℝ)) := by
  have ht0 : 0 < t := by linarith
  have hN0 : 0 < N := by linarith
  have hu : 0 ≤ Real.log t := Real.log_nonneg ht
  have hv : 0 ≤ Real.log N := Real.log_nonneg hN
  have hvu : Real.log N ≤ 43 / 100 * Real.log t := by
    have := Real.log_le_log hN0 hNt
    rwa [Real.log_rpow ht0] at this
  have hLv : Real.log L ≤ Real.log N := Real.log_le_log hL hLN
  have h32 : 0 ≤ Real.log 32 := Real.log_nonneg (by norm_num)
  have hlam : 0 < t / (32 * N ^ 4) := by positivity
  have hloglam : Real.log (t / (32 * N ^ 4)) =
      Real.log t - Real.log 32 - 4 * Real.log N := by
    rw [Real.log_div ht0.ne' (by positivity), Real.log_mul (by norm_num) (by positivity),
      Real.log_pow]
    push_cast
    ring
  have hY : 0 < Real.sqrt N * t ^ (27 / 164 : ℝ) := by positivity
  have hlogY : Real.log (Real.sqrt N * t ^ (27 / 164 : ℝ)) =
      Real.log N / 2 + 27 / 164 * Real.log t := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_sqrt hN0.le, Real.log_rpow ht0]
  constructor
  · refine le_of_log_le (by positivity) hY ?_
    rw [hlogY, Real.log_mul hL.ne' (by positivity), Real.log_rpow hlam, hloglam]
    linarith
  · refine le_of_log_le (by positivity) (by positivity) ?_
    rw [Real.log_mul (by norm_num) hY.ne', hlogY, Real.log_mul (by positivity) (by positivity),
      Real.log_rpow hL, Real.log_rpow hlam, hloglam]
    nlinarith

theorem block_bound_mid :
    ∃ C t₀ : ℝ, 0 < C ∧ ∀ t : ℝ, t₀ ≤ t → ∀ N N' : ℕ, 1 ≤ N → (N : ℝ) ≤ t ^ (43 / 100 : ℝ) →
      N < N' → N' ≤ 2 * N →
      ‖∑ n ∈ Finset.Ioc N N', (n : ℂ) ^ ((t : ℂ) * Complex.I)‖ ≤
        C * Real.sqrt N * t ^ (27 / 164 : ℝ) := by
  obtain ⟨C, hC, hk⟩ := GuthMaynard.SubWeyl.kth_derivative_test 4 (by norm_num) 32 (by norm_num)
  refine ⟨33 * C, 1, by positivity, fun t ht N N' hN hNt hNN' hN'2 => ?_⟩
  have ht0 : 0 < t := by linarith
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hNN'r : (N : ℝ) < N' := by exact_mod_cast hNN'
  have hN'2r : (N' : ℝ) ≤ 2 * N := by exact_mod_cast hN'2
  set c : ℝ := t / (2 * Real.pi) with hc
  set lam : ℝ := t / (32 * (N : ℝ) ^ 4) with hlam
  have hlam0 : 0 < lam := by positivity
  have hsum : ∑ n ∈ Finset.Ioc N N', (n : ℂ) ^ ((t : ℂ) * Complex.I) =
      ∑ n ∈ Finset.Ioc N N', e (Fm c 0 n) := by
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [Finset.mem_Ioc] at hn
    exact natCast_cpow_eq_e t n (by omega)
  have hderiv : ∀ j < 4, ∀ x ∈ Set.Icc (N : ℝ) N', HasDerivAt (Fm c j) (Fm c (j + 1) x) x :=
    fun j hj x hx => Fm_deriv c x (by linarith [hx.1]) j hj
  have hbd : ∀ x ∈ Set.Icc (N : ℝ) N',
      lam ≤ -1 * Fm c 4 x ∧ -1 * Fm c 4 x ≤ 32 * lam := by
    intro x hx
    have hx0 : 0 < x := by linarith [hx.1]
    have hval : -1 * Fm c 4 x = 3 * t / (Real.pi * x ^ 4) := by
      show -1 * (-6 * c * (x ^ 4)⁻¹) = _
      rw [hc]
      field_simp
      ring
    have hpi3 := Real.pi_gt_three
    have hpi4 := Real.pi_le_four
    have hx4 : x ^ 4 ≤ 16 * (N : ℝ) ^ 4 := by
      calc x ^ 4 ≤ (2 * (N : ℝ)) ^ 4 := pow_le_pow_left₀ hx0.le (by linarith [hx.2]) 4
        _ = _ := by ring
    have hx4' : (N : ℝ) ^ 4 ≤ x ^ 4 := pow_le_pow_left₀ hN0.le hx.1 4
    have hN4 : 0 < (N : ℝ) ^ 4 := by positivity
    rw [hval, hlam]
    constructor
    · rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [mul_le_mul_of_nonneg_left hx4 ht0.le, mul_pos ht0 hN4,
        mul_le_mul_of_nonneg_right hpi4 (mul_pos ht0 (pow_pos hx0 4)).le]
    · rw [show 32 * (t / (32 * (N : ℝ) ^ 4)) = t / (N : ℝ) ^ 4 by field_simp,
        div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [mul_le_mul_of_nonneg_left hx4' ht0.le,
        mul_le_mul_of_nonneg_right hpi3.le (mul_pos ht0 (pow_pos hx0 4)).le]
  have key := hk (Fm c) N N' lam (-1) hNN' hlam0 (Or.inr rfl) hderiv hbd
  have e1 : (1 / (2 * (2 : ℝ) ^ (4 - 1) - 2)) = 1 / 14 := by norm_num
  have e2 : (1 - 2 / (2 : ℝ) ^ (4 - 1)) = 3 / 4 := by norm_num
  rw [e1, e2] at key
  obtain ⟨hA1, hA2⟩ := mid_arith t N ((N' : ℝ) - N) ht hN1 hNt (by linarith) (by linarith)
  rw [hsum]
  calc ‖∑ n ∈ Finset.Ioc N N', e (Fm c 0 n)‖
      ≤ C * (((N' : ℝ) - N) * lam ^ (1 / 14 : ℝ) +
          ((N' : ℝ) - N) ^ (3 / 4 : ℝ) * lam ^ (-(1 / 14 : ℝ))) := key
    _ ≤ C * (Real.sqrt N * t ^ (27 / 164 : ℝ) + 32 * (Real.sqrt N * t ^ (27 / 164 : ℝ))) :=
        mul_le_mul_of_nonneg_left (add_le_add hA1 hA2) hC.le
    _ = 33 * C * Real.sqrt N * t ^ (27 / 164 : ℝ) := by ring

end GuthMaynard.SubWeyl.PartM
end

section
namespace GuthMaynard.SubWeyl
/-! ## Part M: blocks with `N ≤ t^{43/100}` -/
alias block_bound_mid := GuthMaynard.SubWeyl.PartM.block_bound_mid

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
theorem em_block_bound (t σ : ℝ) (hσ : 1 / 2 ≤ σ) (ht : 0 < t) (M R : ℕ) (hM1 : 1 ≤ M)
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
    have hblk := em_block_bound t σ hσ ht (T * 2 ^ K) (T * 2 ^ (K + 1)) hM1
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

/-! ## Conjugation -/
theorem cpow_neg_eq_conj (t : ℝ) (n : ℕ) :
    ((n : ℝ) : ℂ) ^ (-((t : ℂ) * I)) = (starRingEnd ℂ) ((n : ℂ) ^ ((t : ℂ) * I)) := by
  have h := Complex.cpow_conj (n : ℂ) ((t : ℂ) * I)
    (by rw [Complex.natCast_arg]; exact Real.pi_ne_zero.symm)
  rw [Complex.conj_natCast] at h
  rw [← h]
  simp

theorem cpow_negreal_eq_conj (t : ℝ) (n : ℕ) :
    (n : ℂ) ^ (((-t : ℝ) : ℂ) * I) = (starRingEnd ℂ) ((n : ℂ) ^ ((t : ℂ) * I)) := by
  rw [← cpow_neg_eq_conj]
  simp

theorem norm_sum_neg (t : ℝ) (s : Finset ℕ) :
    ‖∑ n ∈ s, ((n : ℝ) : ℂ) ^ (-((t : ℂ) * I))‖ = ‖∑ n ∈ s, (n : ℂ) ^ ((t : ℂ) * I)‖ := by
  rw [Finset.sum_congr rfl (fun n _ => cpow_neg_eq_conj t n), ← map_sum, RCLike.norm_conj]

theorem norm_sum_negreal (t : ℝ) (s : Finset ℕ) :
    ‖∑ n ∈ s, (n : ℂ) ^ (((-t : ℝ) : ℂ) * I)‖ = ‖∑ n ∈ s, (n : ℂ) ^ ((t : ℂ) * I)‖ := by
  rw [Finset.sum_congr rfl (fun n _ => cpow_negreal_eq_conj t n), ← map_sum, RCLike.norm_conj]

/-! ## The dual sum -/
theorem dual_bound (t B : ℝ) (hB0 : 0 ≤ B)
    (hyp : ∀ N N' : ℕ, 1 ≤ N → (N : ℝ) ^ 2 ≤ t → N < N' → N' ≤ 2 * N →
      ‖∑ n ∈ Finset.Ioc N N', (n : ℂ) ^ ((t : ℂ) * I)‖ ≤ B * Real.sqrt N)
    (L M : ℕ) (hL : 1 ≤ L) (hM2 : M ≤ 2 * L) (hMt : (M : ℝ) ^ 2 ≤ t) :
    ‖∑ ν ∈ Finset.Icc L M, (ν : ℂ)⁻¹ * (ν : ℂ) ^ (((-t : ℝ) : ℂ) * I)‖ ≤
      (B + 1) / Real.sqrt L := by
  have hLr : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hsL : 1 ≤ Real.sqrt L := Real.one_le_sqrt.mpr hLr
  have hsLsq : Real.sqrt L * Real.sqrt L = L := Real.mul_self_sqrt (by linarith)
  rcases lt_or_ge M L with hML | hLM
  · rw [Finset.Icc_eq_empty (by omega)]
    simp only [Finset.sum_empty, norm_zero]
    positivity
  have hLt : (L : ℝ) ^ 2 ≤ t := by
    have : (L : ℝ) ≤ M := by exact_mod_cast hLM
    nlinarith
  rw [← Finset.sum_Ioc_add_eq_sum_Icc hLM]
  have h1 : ‖(L : ℂ)⁻¹ * (L : ℂ) ^ (((-t : ℝ) : ℂ) * I)‖ ≤ 1 / Real.sqrt L := by
    rw [norm_mul, Complex.norm_natCast_cpow_of_pos (by omega), norm_inv, Complex.norm_natCast]
    have : (((-t : ℝ) : ℂ) * I).re = 0 := by simp
    rw [this, Real.rpow_zero, mul_one, inv_eq_one_div]
    exact one_div_le_one_div_of_le (by linarith) (by nlinarith)
  have h2 : ‖∑ ν ∈ Finset.Ioc L M, (ν : ℂ)⁻¹ * (ν : ℂ) ^ (((-t : ℝ) : ℂ) * I)‖ ≤
      B / Real.sqrt L := by
    by_cases hLM1 : L + 1 ≤ M
    swap
    · rw [Finset.Ioc_eq_empty (by omega)]
      simp only [Finset.sum_empty, norm_zero]
      positivity
    have h := abel_ineq (fun n : ℕ => ((n : ℝ))⁻¹)
      (fun n : ℕ => (n : ℂ) ^ (((-t : ℝ) : ℂ) * I)) (B * Real.sqrt L) L M hLM1
      (fun n hn => by
        have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
        show ((n + 1 : ℕ) : ℝ)⁻¹ ≤ (n : ℝ)⁻¹
        exact inv_anti₀ hn' (by push_cast; linarith))
      (by positivity)
      (fun R' h1 h2 => by
        rw [norm_sum_negreal]
        exact hyp L R' hL hLt h1 (by omega))
    have hcongr : ∑ ν ∈ Finset.Ioc L M, (ν : ℂ)⁻¹ * (ν : ℂ) ^ (((-t : ℝ) : ℂ) * I) =
        ∑ ν ∈ Finset.Ioc L M, (((ν : ℝ)⁻¹ : ℝ) : ℂ) * (ν : ℂ) ^ (((-t : ℝ) : ℂ) * I) := by
      apply Finset.sum_congr rfl
      intro ν _
      push_cast
      rfl
    rw [hcongr]
    refine h.trans ?_
    rw [le_div_iff₀ (by linarith)]
    have hinv : ((L + 1 : ℕ) : ℝ)⁻¹ * (L : ℝ) ≤ 1 := by
      rw [inv_mul_le_iff₀ (by positivity)]
      push_cast; linarith
    calc ((L + 1 : ℕ) : ℝ)⁻¹ * (B * Real.sqrt L) * Real.sqrt L
        = B * (((L + 1 : ℕ) : ℝ)⁻¹ * (Real.sqrt L * Real.sqrt L)) := by ring
      _ = B * (((L + 1 : ℕ) : ℝ)⁻¹ * (L : ℝ)) := by rw [hsLsq]
      _ ≤ B * 1 := mul_le_mul_of_nonneg_left hinv hB0
      _ = B := mul_one B
  calc _ ≤ ‖∑ ν ∈ Finset.Ioc L M, (ν : ℂ)⁻¹ * (ν : ℂ) ^ (((-t : ℝ) : ℂ) * I)‖ +
        ‖(L : ℂ)⁻¹ * (L : ℂ) ^ (((-t : ℝ) : ℂ) * I)‖ := norm_add_le _ _
    _ ≤ B / Real.sqrt L + 1 / Real.sqrt L := add_le_add h2 h1
    _ = _ := by ring

/-! ## Every partial block `(N, R]`, `N ≤ t`, `R ≤ 2N` -/
theorem log_le_four_sqrt (t : ℝ) (ht : 0 ≤ t) (N : ℕ) (hN : 1 ≤ N) (hsq : t < (N : ℝ) ^ 2) :
    Real.log (t + 2) ≤ 4 * Real.sqrt N := by
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  set s := Real.sqrt N with hs
  have hs1 : 1 ≤ s := Real.one_le_sqrt.mpr hNr
  have hss : s ^ 2 = N := Real.sq_sqrt (by linarith)
  have h4 : t + 2 ≤ 3 * s ^ 4 := by
    have e : s ^ 4 = (N : ℝ) ^ 2 := by rw [← hss]; ring
    have : (1 : ℝ) ≤ (N : ℝ) ^ 2 := by nlinarith
    rw [e]; linarith
  have h3 : Real.log 3 ≤ 2 := by
    have := Real.log_le_sub_one_of_pos (x := 3) (by norm_num)
    linarith
  have hls : Real.log s ≤ s - 1 := Real.log_le_sub_one_of_pos (by linarith)
  calc Real.log (t + 2) ≤ Real.log (3 * s ^ 4) := Real.log_le_log (by linarith) h4
    _ = Real.log 3 + 4 * Real.log s := by
        rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]; norm_num
    _ ≤ 4 * s := by linarith

theorem dual_range (t : ℝ) (ht : 4 ≤ t) (N R : ℕ) (hN : 1 ≤ N) (hNR : N < R) (hR : R ≤ 2 * N)
    (hsq : t < (N : ℝ) ^ 2) :
    1 ≤ ⌈t / (2 * Real.pi * R)⌉₊ ∧
      ⌊t / (2 * Real.pi * N)⌋₊ ≤ 2 * ⌈t / (2 * Real.pi * R)⌉₊ ∧
      ((⌊t / (2 * Real.pi * N)⌋₊ : ℕ) : ℝ) ^ 2 ≤ t ∧
      Real.sqrt t ≤ 4 * (Real.sqrt N * Real.sqrt (⌈t / (2 * Real.pi * R)⌉₊ : ℕ)) := by
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have htpos : (0 : ℝ) < t := by linarith
  have hpi3 := Real.pi_gt_three
  have hpi4 := Real.pi_le_four
  have hRr : (N : ℝ) < R := by exact_mod_cast hNR
  have hR2 : (R : ℝ) ≤ 2 * N := by exact_mod_cast hR
  have hRpos : (0 : ℝ) < R := by linarith
  have hx : 0 < t / (2 * Real.pi * R) := by positivity
  have hL1 : 1 ≤ ⌈t / (2 * Real.pi * R)⌉₊ := Nat.ceil_pos.mpr hx
  have hLx : t / (2 * Real.pi * R) ≤ (⌈t / (2 * Real.pi * R)⌉₊ : ℕ) := Nat.le_ceil _
  have hMx : ((⌊t / (2 * Real.pi * N)⌋₊ : ℕ) : ℝ) ≤ t / (2 * Real.pi * N) :=
    Nat.floor_le (by positivity)
  generalize ⌈t / (2 * Real.pi * R)⌉₊ = L at hL1 hLx ⊢
  generalize ⌊t / (2 * Real.pi * N)⌋₊ = M at hMx ⊢
  have hLr : (1 : ℝ) ≤ L := by exact_mod_cast hL1
  have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  have hLx' : t ≤ L * (2 * Real.pi * R) := by rwa [div_le_iff₀ (by positivity)] at hLx
  have hMx' : (M : ℝ) * (2 * Real.pi * N) ≤ t := by rwa [le_div_iff₀ (by positivity)] at hMx
  have hπR : 2 * Real.pi * R ≤ 16 * N := by nlinarith
  have htL : t ≤ 16 * (N * L) := by
    have h1 : (L : ℝ) * (2 * Real.pi * R) ≤ L * (16 * N) :=
      mul_le_mul_of_nonneg_left hπR (by linarith)
    linarith
  have hMN : (M : ℝ) * N ≤ t := by
    have h1 : (M : ℝ) * N ≤ M * (2 * Real.pi * N) :=
      mul_le_mul_of_nonneg_left (by nlinarith) hM0
    linarith
  refine ⟨hL1, ?_, ?_, ?_⟩
  · have h1 : (M : ℝ) * (2 * Real.pi * N) ≤ (2 * L) * (2 * Real.pi * N) := by
      have h2 : (L : ℝ) * (2 * Real.pi * R) ≤ L * (2 * Real.pi * (2 * N)) :=
        mul_le_mul_of_nonneg_left (by nlinarith) (by linarith)
      linarith
    have h3 : (M : ℝ) ≤ 2 * L := le_of_mul_le_mul_right h1 (by positivity)
    have : (M : ℝ) ≤ ((2 * L : ℕ) : ℝ) := by push_cast; linarith
    exact_mod_cast this
  · have hMltN : (M : ℝ) ≤ N := by
      by_contra hcon
      rw [not_le] at hcon
      nlinarith
    nlinarith
  · calc Real.sqrt t ≤ Real.sqrt (16 * (N * L)) := Real.sqrt_le_sqrt htL
      _ = 4 * (Real.sqrt N * Real.sqrt L) := by
          rw [Real.sqrt_mul (by norm_num), Real.sqrt_mul (by linarith),
            show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

theorem err_bound (C t : ℝ) (hC : 0 < C) (ht : 4 ≤ t) (N R : ℕ) (hN : 1 ≤ N) (hNt : (N : ℝ) ≤ t)
    (hR : R ≤ 2 * N) (hsq : t < (N : ℝ) ^ 2) (y₁ y₂ : ℝ) :
    C * (R / t + (R / Real.sqrt t) / (1 + (R / Real.sqrt t) * |y₁|) +
      (R / Real.sqrt t) / (1 + (R / Real.sqrt t) * |y₂|) + Real.log (t + 2)) ≤
      10 * C * Real.sqrt N := by
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hsN : 1 ≤ Real.sqrt N := Real.one_le_sqrt.mpr hNr
  have hsNsq : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt (by linarith)
  have htpos : (0 : ℝ) < t := by linarith
  have hst : 0 < Real.sqrt t := Real.sqrt_pos.mpr htpos
  have hR2 : (R : ℝ) ≤ 2 * N := by exact_mod_cast hR
  have hR0 : (0 : ℝ) ≤ R := Nat.cast_nonneg R
  have hRt : (R : ℝ) / t ≤ 2 := by rw [div_le_iff₀ htpos]; linarith
  have hNst : (N : ℝ) ≤ Real.sqrt N * Real.sqrt t := by
    calc (N : ℝ) = Real.sqrt N * Real.sqrt N := hsNsq.symm
      _ ≤ Real.sqrt N * Real.sqrt t :=
          mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hNt) (by linarith)
  have hRst : (R : ℝ) / Real.sqrt t ≤ 2 * Real.sqrt N := by
    rw [div_le_iff₀ hst]; linarith
  have hRst0 : 0 ≤ (R : ℝ) / Real.sqrt t := div_nonneg hR0 hst.le
  have hwin : ∀ y : ℝ, (R / Real.sqrt t) / (1 + (R / Real.sqrt t) * |y|) ≤ 2 * Real.sqrt N := by
    intro y
    refine le_trans (div_le_self hRst0 ?_) hRst
    have : 0 ≤ (R / Real.sqrt t) * |y| := mul_nonneg hRst0 (abs_nonneg _)
    linarith
  have hlog := log_le_four_sqrt t htpos.le N hN hsq
  refine (mul_le_mul_of_nonneg_left
    (add_le_add (add_le_add (add_le_add hRt (hwin y₁)) (hwin y₂)) hlog) hC.le).trans ?_
  have hc := mul_nonneg hC.le (by linarith : (0 : ℝ) ≤ Real.sqrt N - 1)
  have e : C * (2 + 2 * Real.sqrt N + 2 * Real.sqrt N + 4 * Real.sqrt N) =
      10 * C * Real.sqrt N - 2 * (C * (Real.sqrt N - 1)) := by ring
  rw [e]; linarith

theorem partial_block : ∃ K : ℝ, 0 < K ∧ ∀ t : ℝ, 4 ≤ t → ∀ B : ℝ, 0 ≤ B →
    (∀ N N' : ℕ, 1 ≤ N → (N : ℝ) ^ 2 ≤ t → N < N' → N' ≤ 2 * N →
      ‖∑ n ∈ Finset.Ioc N N', (n : ℂ) ^ ((t : ℂ) * I)‖ ≤ B * Real.sqrt N) →
    ∀ N R : ℕ, 1 ≤ N → (N : ℝ) ≤ t → N < R → R ≤ 2 * N →
      ‖∑ n ∈ Finset.Ioc N R, ((n : ℝ) : ℂ) ^ (-((t : ℂ) * I))‖ ≤
        K * (B + 1) * Real.sqrt N := by
  obtain ⟨C, hC, hw⟩ := GuthMaynard.norm_sum_cpow_sub_dual_window_le
  refine ⟨14 * C + 1, by positivity, fun t ht B hB0 hyp N R hN hNt hNR hR => ?_⟩
  rw [norm_sum_neg]
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hsN : 1 ≤ Real.sqrt N := Real.one_le_sqrt.mpr hNr
  have hBs : 0 ≤ (B + 1) * Real.sqrt N := by positivity
  have hCBs : 0 ≤ C * ((B + 1) * Real.sqrt N) := mul_nonneg hC.le hBs
  have hCs : C * Real.sqrt N ≤ C * ((B + 1) * Real.sqrt N) :=
    mul_le_mul_of_nonneg_left (by nlinarith) hC.le
  by_cases hsq : (N : ℝ) ^ 2 ≤ t
  · calc _ ≤ B * Real.sqrt N := hyp N R hN hsq hNR hR
      _ ≤ (14 * C + 1) * (B + 1) * Real.sqrt N := by nlinarith
  rw [not_le] at hsq
  obtain ⟨G, hG, hmain⟩ := hw N R hN hNR (by omega) t (by linarith)
  obtain ⟨hL1, hM2L, hMsq, hstL⟩ := dual_range t ht N R hN hNR hR hsq
  have herr := hmain.trans (err_bound C t hC ht N R hN hNt hR hsq _ _)
  have hD := dual_bound t B hB0 hyp _ _ hL1 hM2L hMsq
  generalize ⌈t / (2 * Real.pi * R)⌉₊ = L at hL1 hD hstL herr
  generalize ⌊t / (2 * Real.pi * N)⌋₊ = M at hD herr
  generalize (∑ ν ∈ Finset.Icc L M, (ν : ℂ)⁻¹ * (ν : ℂ) ^ (((-t : ℝ) : ℂ) * I)) = D at hD herr
  have hLr : (1 : ℝ) ≤ L := by exact_mod_cast hL1
  have hsL : 0 < Real.sqrt L := Real.sqrt_pos.mpr (by linarith)
  have hGD : ‖G * D‖ ≤ 4 * C * ((B + 1) * Real.sqrt N) := by
    rw [norm_mul]
    have hq : Real.sqrt t / Real.sqrt L ≤ 4 * Real.sqrt N := by
      rw [div_le_iff₀ hsL]; linarith
    calc ‖G‖ * ‖D‖ ≤ (C * Real.sqrt t) * ((B + 1) / Real.sqrt L) :=
          mul_le_mul hG hD (norm_nonneg _) (by positivity)
      _ = C * (B + 1) * (Real.sqrt t / Real.sqrt L) := by ring
      _ ≤ C * (B + 1) * (4 * Real.sqrt N) :=
          mul_le_mul_of_nonneg_left hq (by positivity)
      _ = _ := by ring
  calc ‖∑ n ∈ Finset.Ioc N R, (n : ℂ) ^ ((t : ℂ) * I)‖
      ≤ ‖(∑ n ∈ Finset.Ioc N R, (n : ℂ) ^ ((t : ℂ) * I)) - G * D‖ + ‖G * D‖ :=
        norm_le_norm_sub_add _ _
    _ ≤ 10 * C * Real.sqrt N + 4 * C * ((B + 1) * Real.sqrt N) := add_le_add herr hGD
    _ ≤ (14 * C + 1) * (B + 1) * Real.sqrt N := by linarith

/-! ## The dyadic decomposition -/
theorem dyadic_block (K t B : ℝ) (hK : 0 < K) (hB0 : 0 ≤ B) (j T : ℕ) (hT : (T : ℝ) ≤ t)
    (hj : 2 ^ j < T)
    (hblk : ∀ N R : ℕ, 1 ≤ N → (N : ℝ) ≤ t → N < R → R ≤ 2 * N →
      ‖∑ n ∈ Finset.Ioc N R, ((n : ℝ) : ℂ) ^ (-((t : ℂ) * I))‖ ≤ K * (B + 1) * Real.sqrt N) :
    ‖∑ n ∈ Finset.Ioc (2 ^ j) (min (2 ^ (j + 1)) T),
        ((n : ℝ) : ℂ) ^ (-(((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I))‖ ≤ K * (B + 1) := by
  have hN : 1 ≤ 2 ^ j := Nat.one_le_two_pow
  have hNt : ((2 ^ j : ℕ) : ℝ) ≤ t := by
    have : ((2 ^ j : ℕ) : ℝ) < T := by exact_mod_cast hj
    linarith
  have hNpos : (0 : ℝ) < ((2 ^ j : ℕ) : ℝ) := by positivity
  have h := abel_block (1 / 2) t (K * (B + 1) * Real.sqrt ((2 ^ j : ℕ) : ℝ))
    (by norm_num) (by positivity) (2 ^ j) (min (2 ^ (j + 1)) T) hN
    (fun R' h1 h2 => hblk (2 ^ j) R' hN hNt h1
      (by have := min_le_left (2 ^ (j + 1)) T; rw [pow_succ] at this; omega))
  refine h.trans (le_of_eq ?_)
  rw [Real.sqrt_eq_rpow]
  have : ((2 ^ j : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) * ((2 ^ j : ℕ) : ℝ) ^ (1 / 2 : ℝ) = 1 := by
    rw [← Real.rpow_add hNpos]; norm_num
  calc _ = K * (B + 1) * (((2 ^ j : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) * ((2 ^ j : ℕ) : ℝ) ^ (1 / 2 : ℝ)) := by
        ring
    _ = _ := by rw [this, mul_one]

theorem dyadic_sum (K t B : ℝ) (hK : 0 < K) (hB0 : 0 ≤ B) (ht : 2 ≤ t)
    (hblk : ∀ N R : ℕ, 1 ≤ N → (N : ℝ) ≤ t → N < R → R ≤ 2 * N →
      ‖∑ n ∈ Finset.Ioc N R, ((n : ℝ) : ℂ) ^ (-((t : ℂ) * I))‖ ≤ K * (B + 1) * Real.sqrt N) :
    ‖∑ n ∈ Finset.Icc 1 ⌊t⌋₊, ((n : ℝ) : ℂ) ^ (-(((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I))‖ ≤
      1 + (⌊Real.log t / Real.log 2⌋₊ + 1 : ℕ) * (K * (B + 1)) := by
  set T := ⌊t⌋₊ with hTdef
  set J := ⌊Real.log t / Real.log 2⌋₊ with hJdef
  set f : ℕ → ℂ := fun n => ((n : ℝ) : ℂ) ^ (-(((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)) with hf
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
  have htel : ∀ K', ∑ n ∈ Finset.Ioc (m 0) (m K'), f n =
      ∑ j ∈ Finset.range K', ∑ n ∈ Finset.Ioc (m j) (m (j + 1)), f n := by
    intro K'
    induction K' with
    | zero => simp
    | succ K' ih =>
      rw [Finset.sum_range_succ, ← ih,
        Finset.sum_Ioc_consecutive _ (hmono (Nat.zero_le K')) (hmono1 K')]
  have hm0 : m 0 = 1 := by simp [hm]; omega
  have hmJ : m (J + 1) = T := by simp [hm]; omega
  have hsplit : ∑ n ∈ Finset.Icc 1 T, f n = f 1 + ∑ n ∈ Finset.Ioc (m 0) (m (J + 1)), f n := by
    rw [hm0, hmJ, show Finset.Icc 1 T = Finset.Ioc 0 T by ext x; simp; omega,
      ← Finset.sum_Ioc_consecutive _ (Nat.zero_le 1) hT1]
    simp
  have hblock : ∀ j ∈ Finset.range (J + 1), ‖∑ n ∈ Finset.Ioc (m j) (m (j + 1)), f n‖ ≤
      K * (B + 1) := by
    intro j _
    by_cases hj : 2 ^ j < T
    · have e1 : m j = 2 ^ j := min_eq_left hj.le
      rw [e1]
      exact dyadic_block K t B hK hB0 j T hTt hj hblk
    · have e1 : m j = T := min_eq_right (not_lt.mp hj)
      have e2 : m (j + 1) = T :=
        min_eq_right ((not_lt.mp hj).trans (Nat.pow_le_pow_right (by norm_num) (by omega)))
      rw [e1, e2, Finset.Ioc_self]
      simp only [Finset.sum_empty, norm_zero]
      positivity
  have hf1 : ‖f 1‖ = 1 := by simp [hf]
  rw [hsplit, htel]
  calc _ ≤ ‖f 1‖ + ‖∑ j ∈ Finset.range (J + 1), ∑ n ∈ Finset.Ioc (m j) (m (j + 1)), f n‖ :=
        norm_add_le _ _
    _ ≤ 1 + ∑ _j ∈ Finset.range (J + 1), K * (B + 1) := by
      rw [hf1]
      exact add_le_add le_rfl ((norm_sum_le _ _).trans (Finset.sum_le_sum hblock))
    _ = _ := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-! ## The stub -/
theorem zeta_le_blocks :
    ∃ C t₀ : ℝ, 0 < C ∧ 2 ≤ t₀ ∧ ∀ t : ℝ, t₀ ≤ t → ∀ B : ℝ, 0 ≤ B →
      (∀ N N' : ℕ, 1 ≤ N → (N : ℝ) ^ 2 ≤ t → N < N' → N' ≤ 2 * N →
        ‖∑ n ∈ Finset.Ioc N N', (n : ℂ) ^ ((t : ℂ) * Complex.I)‖ ≤ B * Real.sqrt N) →
      ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C * (B + 1) * Real.log t := by
  obtain ⟨K₀, t₁, hK₀, happ⟩ := approx_formula
  obtain ⟨K, hK, hpb⟩ := partial_block
  refine ⟨K₀ + 1 + 3 * K, max t₁ 4, by positivity, le_max_of_le_right (by norm_num),
    fun t ht B hB0 hyp => ?_⟩
  have ht1 : t₁ ≤ t := le_trans (le_max_left _ _) ht
  have ht4 : (4 : ℝ) ≤ t := le_trans (le_max_right _ _) ht
  have h1 := happ t ht1 (1 / 2) le_rfl (by norm_num)
  have h2 := dyadic_sum K t B hK hB0 (by linarith) (hpb t ht4 B hB0 hyp)
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl2' : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have := Real.log_two_gt_d9; linarith
  have hlog : 1 ≤ Real.log t := by
    have h4 : Real.log 4 ≤ Real.log t := Real.log_le_log (by norm_num) ht4
    have e : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    linarith
  have hJ : ((⌊Real.log t / Real.log 2⌋₊ + 1 : ℕ) : ℝ) ≤ 3 * Real.log t := by
    have hfl : (⌊Real.log t / Real.log 2⌋₊ : ℝ) ≤ Real.log t / Real.log 2 :=
      Nat.floor_le (by positivity)
    have hdiv : Real.log t / Real.log 2 ≤ 2 * Real.log t := by
      rw [div_le_iff₀ hl2]; nlinarith
    push_cast; linarith
  have hKB : 0 ≤ K * (B + 1) := by positivity
  have htri : ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ≤
      K₀ + (1 + 3 * Real.log t * (K * (B + 1))) := by
    calc _ ≤ ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) -
            ∑ n ∈ Finset.Icc 1 ⌊t⌋₊, ((n : ℝ) : ℂ) ^ (-(((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I))‖ +
          ‖∑ n ∈ Finset.Icc 1 ⌊t⌋₊, ((n : ℝ) : ℂ) ^ (-(((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I))‖ :=
          norm_le_norm_sub_add _ _
      _ ≤ K₀ + (1 + 3 * Real.log t * (K * (B + 1))) :=
          add_le_add h1 (h2.trans (by gcongr))
  refine htri.trans ?_
  have hx : (K₀ + 1) ≤ (K₀ + 1) * ((B + 1) * Real.log t) := by
    have : 1 ≤ (B + 1) * Real.log t := by nlinarith
    nlinarith
  nlinarith

end GuthMaynard.SubWeyl.PartZ
end

section
namespace GuthMaynard.SubWeyl
/-! ## Part Z: `ζ(1/2+it)` and blocks of length at most `√t` -/
alias zeta_le_blocks := GuthMaynard.SubWeyl.PartZ.zeta_le_blocks

/-! ## Assembly (no `sorry` below) -/
/-- The key proposition: every block `N < n ≤ N' ≤ 2N` with `N ≤ √t`. -/
theorem block_bound :
    ∃ C t₀ : ℝ, 0 < C ∧ ∀ t : ℝ, t₀ ≤ t → ∀ N N' : ℕ, 1 ≤ N → (N : ℝ) ^ 2 ≤ t →
      N < N' → N' ≤ 2 * N →
      ‖∑ n ∈ Finset.Ioc N N', (n : ℂ) ^ ((t : ℂ) * Complex.I)‖ ≤
        C * Real.sqrt N * t ^ (27 / 164 : ℝ) := by
  obtain ⟨C₁, t₁, hC₁, h₁⟩ := block_bound_mid
  obtain ⟨C₂, t₂, hC₂, h₂⟩ := block_bound_large
  refine ⟨max C₁ C₂, max (max t₁ t₂) 1, lt_max_of_lt_left hC₁, fun t ht N N' hN hNt hNN' hN'2 => ?_⟩
  have ht1 : t₁ ≤ t := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) ht
  have ht2 : t₂ ≤ t := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) ht
  have ht0 : (0 : ℝ) < t := lt_of_lt_of_le one_pos (le_trans (le_max_right _ _) ht)
  have hnn : 0 ≤ Real.sqrt N * t ^ (27 / 164 : ℝ) := by positivity
  rcases le_total (N : ℝ) (t ^ (43 / 100 : ℝ)) with hle | hge
  · calc _ ≤ C₁ * Real.sqrt N * t ^ (27 / 164 : ℝ) := h₁ t ht1 N N' hN hle hNN' hN'2
      _ = C₁ * (Real.sqrt N * t ^ (27 / 164 : ℝ)) := by ring
      _ ≤ max C₁ C₂ * (Real.sqrt N * t ^ (27 / 164 : ℝ)) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hnn
      _ = _ := by ring
  · calc _ ≤ C₂ * Real.sqrt N * t ^ (27 / 164 : ℝ) := h₂ t ht2 N N' hge hNt hNN' hN'2
      _ = C₂ * (Real.sqrt N * t ^ (27 / 164 : ℝ)) := by ring
      _ ≤ max C₁ C₂ * (Real.sqrt N * t ^ (27 / 164 : ℝ)) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) hnn
      _ = _ := by ring

/-- `ζ(1/2+it) ≪ t^{27/164} log t`. -/
theorem zeta_half_bound :
    ∃ C t₀ : ℝ, 0 < C ∧ 2 ≤ t₀ ∧ ∀ t : ℝ, t₀ ≤ t →
      ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ ≤
        C * (t ^ (27 / 164 : ℝ) * Real.log t) := by
  obtain ⟨C₁, t₁, hC₁, h₁⟩ := block_bound
  obtain ⟨C₀, t₀, hC₀, ht₀, h₀⟩ := zeta_le_blocks
  refine ⟨C₀ * (C₁ + 1), max t₀ t₁, by positivity, le_max_of_le_left ht₀, fun t ht => ?_⟩
  have ht0' : t₀ ≤ t := le_trans (le_max_left _ _) ht
  have ht1' : t₁ ≤ t := le_trans (le_max_right _ _) ht
  have ht2 : (2 : ℝ) ≤ t := le_trans ht₀ ht0'
  have hpow : (1 : ℝ) ≤ t ^ (27 / 164 : ℝ) :=
    Real.one_le_rpow (by linarith) (by norm_num)
  have hlog : 0 ≤ Real.log t := Real.log_nonneg (by linarith)
  have hB : (0 : ℝ) ≤ C₁ * t ^ (27 / 164 : ℝ) := by positivity
  have key := h₀ t ht0' (C₁ * t ^ (27 / 164 : ℝ)) hB (fun N N' hN hNt hNN' hN'2 => by
    calc _ ≤ C₁ * Real.sqrt N * t ^ (27 / 164 : ℝ) := h₁ t ht1' N N' hN hNt hNN' hN'2
      _ = _ := by ring)
  calc _ ≤ C₀ * (C₁ * t ^ (27 / 164 : ℝ) + 1) * Real.log t := key
    _ ≤ C₀ * (C₁ * t ^ (27 / 164 : ℝ) + t ^ (27 / 164 : ℝ)) * Real.log t := by
        gcongr
    _ = _ := by ring

/-- The target (published as `GuthMaynard.mu_half_le_twentyseven_div_onesixtyfour`). -/
theorem mu_half_le_twentyseven_div_onesixtyfour :
    LindelofHypothesis.mu (1 / 2) ≤ ((27 / 164 : ℝ) : EReal) := by
  obtain ⟨C, t₀, hC, ht₀, hb⟩ := zeta_half_bound
  have hmem : ∀ a : ℝ, 27 / 164 < a →
      LindelofHypothesis.mu (1 / 2) ≤ (a : EReal) := by
    intro a ha
    unfold LindelofHypothesis.mu
    refine sInf_le ⟨a, ?_, rfl⟩
    show (fun T : ℝ => riemannZeta (((1 / 2 : ℝ) : ℂ) + (T : ℂ) * Complex.I)) =O[Filter.atTop]
      (fun T : ℝ => T ^ a)
    have h1 : (fun T : ℝ => riemannZeta (((1 / 2 : ℝ) : ℂ) + (T : ℂ) * Complex.I))
        =O[Filter.atTop] (fun T : ℝ => T ^ (27 / 164 : ℝ) * Real.log T) := by
      refine Asymptotics.IsBigO.of_bound C ?_
      filter_upwards [Filter.eventually_ge_atTop t₀] with t ht
      have hnn : 0 ≤ t ^ (27 / 164 : ℝ) * Real.log t :=
        mul_nonneg (Real.rpow_nonneg (by linarith) _) (Real.log_nonneg (by linarith))
      rw [Real.norm_of_nonneg hnn]
      exact hb t ht
    have h2 : (fun T : ℝ => T ^ (27 / 164 : ℝ) * Real.log T) =O[Filter.atTop]
        (fun T : ℝ => T ^ (27 / 164 : ℝ) * T ^ (a - 27 / 164)) :=
      (Asymptotics.isBigO_refl _ _).mul
        (isLittleO_log_rpow_atTop (by linarith : 0 < a - 27 / 164)).isBigO
    have h3 : (fun T : ℝ => T ^ (27 / 164 : ℝ) * T ^ (a - 27 / 164)) =ᶠ[Filter.atTop]
        (fun T : ℝ => T ^ a) := by
      filter_upwards [Filter.eventually_gt_atTop 0] with t ht
      rw [← Real.rpow_add ht]
      congr 1
      ring
    exact (h1.trans h2).trans_eventuallyEq h3
  by_contra hcon
  rw [not_le] at hcon
  obtain ⟨a, ha1, ha2⟩ := EReal.lt_iff_exists_real_btwn.mp hcon
  exact absurd (hmem a (by exact_mod_cast ha1)) (not_le.mpr ha2)

end GuthMaynard.SubWeyl
end

section
open GuthMaynard
open GuthMaynard.SubWeyl
theorem solution :
    LindelofHypothesis.mu (1 / 2) ≤ ((27 / 164 : ℝ) : EReal) := by
  exact GuthMaynard.SubWeyl.mu_half_le_twentyseven_div_onesixtyfour
end
