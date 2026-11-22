-- Prove2me | solution 1 for MasulloGRH.dirichlet_polynomials_on_one_line_of_region_bound
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-21T18:21:43.722476+00:00
-- url     : https://prove2.me/submissions/ebfb9bec-beb8-4c3a-8720-c274f14e09ac

import Mathlib
import Theorems.Thm_SWPort_Davenport_perron_of_region_bound

set_option autoImplicit false
set_option linter.all false

/-!
# Perron's formula on the line `Re s = 1`

Let `|a_n| ≤ M Λ(n)` and let `G` continue `∑ a_n n^{-s}` analytically to the region
`σ ≥ 1 - c / log (|t| + 3)` away from `p = 1 + i t₀`, with `|G(s) - r/(s - p)| ≤ C log² (|t| + 3)`
there.  Then `∑_{n ≤ N} a_n n^{-s} - r N^{p-s}/(p-s) → G(s)` locally uniformly on the line
`Re s = 1` away from `p`.

* `perron_uniform`: the quantitative Perron theorem `SWPort.Davenport.perron_of_region_bound`,
  applied to the shifted coefficients `a_n n^{-(s-1)}`, uniformly for `s` in a rectangle.
* `cauchy_bound`: partial summation, giving a uniform Cauchy bound for the Dirichlet polynomials.
* `main`: the limit is identified by continuity from the half-plane `Re s > 1`.
-/

-- ===== DP1 =====


namespace MasulloGRH.DP

open Filter Topology

/-! ### Elementary estimates -/

/-- Telescoping bound. -/
lemma tele (F : ℕ → ℂ) (T : ℕ → ℝ) (M : ℕ)
    (h : ∀ n, M ≤ n → ‖F (n + 1) - F n‖ ≤ T n - T (n + 1)) (k : ℕ) :
    ‖F (M + k) - F M‖ ≤ T M - T (M + k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h1 := h (M + k) (Nat.le_add_right _ _)
    calc ‖F (M + (k + 1)) - F M‖
        = ‖(F (M + k + 1) - F (M + k)) + (F (M + k) - F M)‖ := by
          rw [← add_assoc]; congr 1; ring
      _ ≤ ‖F (M + k + 1) - F (M + k)‖ + ‖F (M + k) - F M‖ := norm_add_le _ _
      _ ≤ (T (M + k) - T (M + k + 1)) + (T M - T (M + k)) := add_le_add h1 ih
      _ = T M - T (M + (k + 1)) := by rw [← add_assoc]; ring

/-- Second order Taylor bound for `(1 + θ)^α`. -/
lemma taylor (α : ℂ) (θ A : ℝ) (hA : 1 ≤ A) (hα : ‖α‖ ≤ A) (hθ : |θ| ≤ 1 / (4 * A)) :
    ‖Complex.exp (α * (Real.log (1 + θ) : ℂ)) - 1 - α * θ‖ ≤ 6 * A ^ 2 * θ ^ 2 := by
  have hA0 : 0 < A := by linarith
  have hθ4 : |θ| ≤ 1 / 4 := hθ.trans (by
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith)
  have hAθ : A * |θ| ≤ 1 / 4 := by
    have := mul_le_mul_of_nonneg_left hθ hA0.le
    rwa [show A * (1 / (4 * A)) = 1 / 4 by field_simp] at this
  have hlog : |Real.log (1 + θ) - θ| ≤ 2 * θ ^ 2 := by
    have h := Real.abs_log_sub_add_sum_range_le (x := -θ) (by rw [abs_neg]; linarith) 1
    simp only [Finset.range_one, Finset.sum_singleton, zero_add, pow_one, Nat.cast_zero,
      div_one, abs_neg, sub_neg_eq_add] at h
    have h2 : |θ| ^ (1 + 1) / (1 - |θ|) ≤ 2 * θ ^ 2 := by
      rw [div_le_iff₀ (by linarith), show (1 + 1 : ℕ) = 2 by norm_num, sq_abs]
      nlinarith [sq_nonneg θ]
    have h3 : |Real.log (1 + θ) - θ| = |-θ + Real.log (1 + θ)| := by congr 1; ring
    rw [h3]
    exact h.trans h2
  have hL : |Real.log (1 + θ)| ≤ 2 * |θ| := by
    have h1 : |Real.log (1 + θ)| ≤ |Real.log (1 + θ) - θ| + |θ| := by
      have := abs_add_le (Real.log (1 + θ) - θ) θ
      simpa using this
    have h2 : 2 * θ ^ 2 ≤ |θ| := by
      rw [← sq_abs]; nlinarith [abs_nonneg θ]
    linarith
  set L := Real.log (1 + θ) with hLdef
  have hz : ‖α * (L : ℂ)‖ ≤ 2 * A * |θ| := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc ‖α‖ * |L| ≤ A * (2 * |θ|) := mul_le_mul hα hL (abs_nonneg _) hA0.le
      _ = 2 * A * |θ| := by ring
  have hz1 : ‖α * (L : ℂ)‖ ≤ 1 := by linarith
  have h1 := Complex.norm_exp_sub_one_sub_id_le hz1
  have h2 : ‖α * (L : ℂ) - α * θ‖ ≤ 2 * A * θ ^ 2 := by
    rw [← mul_sub, norm_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    calc ‖α‖ * |L - θ| ≤ A * (2 * θ ^ 2) := mul_le_mul hα hlog (abs_nonneg _) hA0.le
      _ = 2 * A * θ ^ 2 := by ring
  have h3 : ‖α * (L : ℂ)‖ ^ 2 ≤ 4 * A ^ 2 * θ ^ 2 := by
    calc ‖α * (L : ℂ)‖ ^ 2 ≤ (2 * A * |θ|) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hz 2
      _ = 4 * A ^ 2 * θ ^ 2 := by rw [mul_pow, mul_pow, sq_abs]; ring
  have h4 : 2 * A * θ ^ 2 ≤ 2 * A ^ 2 * θ ^ 2 := by nlinarith [sq_nonneg θ]
  calc ‖Complex.exp (α * (L : ℂ)) - 1 - α * θ‖
      = ‖(Complex.exp (α * (L : ℂ)) - 1 - α * (L : ℂ)) + (α * (L : ℂ) - α * θ)‖ := by
        congr 1; ring
    _ ≤ ‖Complex.exp (α * (L : ℂ)) - 1 - α * (L : ℂ)‖ + ‖α * (L : ℂ) - α * θ‖ := norm_add_le _ _
    _ ≤ 6 * A ^ 2 * θ ^ 2 := by linarith

lemma succ_cpow (n : ℕ) (hn : 1 ≤ n) (α : ℂ) :
    ((n + 1 : ℕ) : ℂ) ^ α =
      (n : ℂ) ^ α * Complex.exp (α * (Real.log (1 + 1 / (n : ℝ)) : ℂ)) := by
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have h1 : ((n + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  have h2 : (n : ℂ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hl : Real.log ((n + 1 : ℕ) : ℝ) = Real.log (n : ℝ) + Real.log (1 + 1 / (n : ℝ)) := by
    rw [← Real.log_mul hn0 (by positivity)]
    congr 1
    push_cast
    field_simp
  rw [Complex.cpow_def_of_ne_zero h1, Complex.cpow_def_of_ne_zero h2, ← Complex.natCast_log,
    ← Complex.natCast_log, ← Complex.exp_add, hl]
  congr 1
  push_cast
  ring

lemma pred_cpow (m : ℕ) (hm : 1 ≤ m) (α : ℂ) :
    (m : ℂ) ^ α =
      ((m + 1 : ℕ) : ℂ) ^ α * Complex.exp (α * (Real.log (1 + -(1 / ((m + 1 : ℕ) : ℝ))) : ℂ)) := by
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  have hm1 : (((m + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  have h1 : ((m + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
  have h2 : (m : ℂ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  have hpos : (0 : ℝ) < 1 + -(1 / ((m + 1 : ℕ) : ℝ)) := by
    have : (1 : ℝ) / ((m + 1 : ℕ) : ℝ) < 1 := by
      rw [div_lt_one (by positivity)]; push_cast; linarith [show (1 : ℝ) ≤ m by exact_mod_cast hm]
    linarith
  have hl : Real.log (m : ℝ) =
      Real.log ((m + 1 : ℕ) : ℝ) + Real.log (1 + -(1 / ((m + 1 : ℕ) : ℝ))) := by
    rw [← Real.log_mul hm1 hpos.ne']
    congr 1
    push_cast
    field_simp
    ring
  rw [Complex.cpow_def_of_ne_zero h1, Complex.cpow_def_of_ne_zero h2, ← Complex.natCast_log,
    ← Complex.natCast_log, ← Complex.exp_add, hl]
  congr 1
  push_cast
  ring

/-- The increment of the model sequence is `O(1/n²)`. -/
lemma U_bound (w : ℂ) (A δ : ℝ) (hA : 1 ≤ A) (hw : ‖w‖ ≤ A) (hw1 : ‖1 + w‖ ≤ A) (hδ : 0 < δ)
    (hwδ : δ ≤ ‖w‖) (hw1' : 1 / 2 ≤ ‖1 + w‖) (hre : w.re ≤ 0) (m : ℕ) (hm : 1 ≤ m)
    (hmA : 4 * A ≤ ((m + 1 : ℕ) : ℝ)) :
    ‖(((m + 1 + 1 : ℕ) : ℂ) ^ (1 + w) - ((m + 1 : ℕ) : ℂ) ^ (1 + w)) /
          ((1 + w) * ((m + 1 : ℕ) : ℂ)) -
        (((m + 1 : ℕ) : ℂ) ^ w - (m : ℂ) ^ w) / w‖ ≤
      6 * A ^ 2 * (2 + 1 / δ) / ((m + 1 : ℕ) : ℝ) ^ 2 := by
  set n : ℕ := m + 1 with hn
  have hn1 : 1 ≤ n := by omega
  have hnR : (0 : ℝ) < (n : ℝ) := by positivity
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hw0 : w ≠ 0 := norm_pos_iff.1 (lt_of_lt_of_le hδ hwδ)
  have hw10 : 1 + w ≠ 0 := norm_pos_iff.1 (lt_of_lt_of_le (by norm_num) hw1')
  have hθ : |1 / (n : ℝ)| ≤ 1 / (4 * A) := by
    rw [abs_of_pos (by positivity)]
    exact one_div_le_one_div_of_le (by linarith) hmA
  have hθ' : |-(1 / (n : ℝ))| ≤ 1 / (4 * A) := by rwa [abs_neg]
  set R1 := Complex.exp ((1 + w) * (Real.log (1 + 1 / (n : ℝ)) : ℂ)) - 1 - (1 + w) * ((1 / (n : ℝ) : ℝ) : ℂ)
    with hR1
  set R2 := Complex.exp (w * (Real.log (1 + -(1 / (n : ℝ))) : ℂ)) - 1 - w * ((-(1 / (n : ℝ)) : ℝ) : ℂ)
    with hR2
  have b1 : ‖R1‖ ≤ 6 * A ^ 2 * (1 / (n : ℝ)) ^ 2 := taylor (1 + w) _ A hA hw1 hθ
  have b2 : ‖R2‖ ≤ 6 * A ^ 2 * (-(1 / (n : ℝ))) ^ 2 := taylor w _ A hA hw hθ'
  have e1 : ((n + 1 : ℕ) : ℂ) ^ (1 + w) = (n : ℂ) ^ (1 + w) * (R1 + 1 + (1 + w) / (n : ℂ)) := by
    rw [succ_cpow n hn1, hR1]; push_cast; ring
  have e2 : (m : ℂ) ^ w = (n : ℂ) ^ w * (R2 + 1 - w / (n : ℂ)) := by
    have e2' := pred_cpow m hm w
    rw [← hn] at e2'
    rw [e2', hR2, show ((-(1 / (n : ℝ)) : ℝ) : ℂ) = -(1 / (n : ℂ)) by push_cast; ring]
    ring
  have e3 : (n : ℂ) ^ (1 + w) = (n : ℂ) * (n : ℂ) ^ w := by
    rw [Complex.cpow_add _ _ hnC, Complex.cpow_one]
  have key : (((n + 1 : ℕ) : ℂ) ^ (1 + w) - (n : ℂ) ^ (1 + w)) / ((1 + w) * (n : ℂ)) -
      ((n : ℂ) ^ w - (m : ℂ) ^ w) / w = (n : ℂ) ^ w * (R1 / (1 + w) + R2 / w) := by
    rw [e1, e2, e3]
    field_simp
    ring
  rw [key, norm_mul]
  have hnw : ‖(n : ℂ) ^ w‖ ≤ 1 := by
    rw [Complex.norm_natCast_cpow_of_pos (by omega)]
    exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hn1) hre
  have c1 : ‖R1 / (1 + w)‖ ≤ 6 * A ^ 2 * (1 / (n : ℝ)) ^ 2 * 2 := by
    rw [norm_div, div_le_iff₀ (lt_of_lt_of_le (by norm_num) hw1')]
    have : 0 ≤ 6 * A ^ 2 * (1 / (n : ℝ)) ^ 2 := by positivity
    nlinarith
  have c2 : ‖R2 / w‖ ≤ 6 * A ^ 2 * (1 / (n : ℝ)) ^ 2 * (1 / δ) := by
    rw [norm_div, div_le_iff₀ (lt_of_lt_of_le hδ hwδ)]
    have h0 : 0 ≤ 6 * A ^ 2 * (1 / (n : ℝ)) ^ 2 := by positivity
    rw [neg_sq] at b2
    calc ‖R2‖ ≤ 6 * A ^ 2 * (1 / (n : ℝ)) ^ 2 := b2
      _ = 6 * A ^ 2 * (1 / (n : ℝ)) ^ 2 * (1 / δ) * δ := by field_simp
      _ ≤ 6 * A ^ 2 * (1 / (n : ℝ)) ^ 2 * (1 / δ) * ‖w‖ :=
          mul_le_mul_of_nonneg_left hwδ (by positivity)
  calc ‖(n : ℂ) ^ w‖ * ‖R1 / (1 + w) + R2 / w‖ ≤ 1 * (‖R1 / (1 + w)‖ + ‖R2 / w‖) :=
        mul_le_mul hnw (norm_add_le _ _) (norm_nonneg _) zero_le_one
    _ ≤ 6 * A ^ 2 * (2 + 1 / δ) / (n : ℝ) ^ 2 := by
        rw [one_mul]
        have : 6 * A ^ 2 * (2 + 1 / δ) / (n : ℝ) ^ 2 =
            6 * A ^ 2 * (1 / (n : ℝ)) ^ 2 * 2 + 6 * A ^ 2 * (1 / (n : ℝ)) ^ 2 * (1 / δ) := by
          field_simp
        rw [this]
        exact add_le_add c1 c2

/-- Decay of the de la Vallée Poussin error. -/
lemma eps_le (c₁ : ℝ) (hc₁ : 0 < c₁) (n : ℕ) (hn : 2 ≤ n) :
    Real.exp (-c₁ * Real.sqrt (Real.log n)) ≤ 24 / c₁ ^ 4 / (Real.log n) ^ 2 := by
  have hlog : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn)
  set y := Real.sqrt (Real.log n) with hy
  have hy0 : 0 < y := Real.sqrt_pos.2 hlog
  have hy2 : y ^ 2 = Real.log n := Real.sq_sqrt hlog.le
  have h := Real.pow_div_factorial_le_exp (c₁ * y) (by positivity) 4
  rw [show (Nat.factorial 4 : ℝ) = 24 by norm_num [Nat.factorial]] at h
  rw [neg_mul, Real.exp_neg, ← hy2]
  rw [inv_le_comm₀ (Real.exp_pos _) (by positivity)]
  refine le_trans (le_of_eq ?_) h
  field_simp

/-- `1 / (n log² (n+1)) ≤ 2 (1 / log n - 1 / log (n+1))`. -/
lemma log_tele (n : ℕ) (hn : 2 ≤ n) :
    1 / ((n : ℝ) * (Real.log ((n + 1 : ℕ) : ℝ)) ^ 2) ≤
      2 * (1 / Real.log n - 1 / Real.log ((n + 1 : ℕ) : ℝ)) := by
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have h0 : 0 < Real.log (n : ℝ) := Real.log_pos (by linarith)
  have h1 : Real.log (n : ℝ) ≤ Real.log ((n + 1 : ℕ) : ℝ) :=
    Real.log_le_log (by linarith) (by push_cast; linarith)
  have h2 : 0 < Real.log ((n + 1 : ℕ) : ℝ) := lt_of_lt_of_le h0 h1
  have hd : 1 / (2 * (n : ℝ)) ≤ Real.log ((n + 1 : ℕ) : ℝ) - Real.log n := by
    rw [← Real.log_div (by positivity) (by positivity)]
    have h3 : (0 : ℝ) < (n : ℝ) / ((n + 1 : ℕ) : ℝ) := by positivity
    have h4 := Real.log_le_sub_one_of_pos h3
    rw [Real.log_div (by positivity) (by positivity)] at h4
    rw [Real.log_div (by positivity) (by positivity)]
    have h5 : (n : ℝ) / ((n + 1 : ℕ) : ℝ) - 1 = -(1 / ((n : ℝ) + 1)) := by
      push_cast; field_simp; ring
    have h6 : 1 / (2 * (n : ℝ)) ≤ 1 / ((n : ℝ) + 1) :=
      one_div_le_one_div_of_le (by linarith) (by linarith)
    linarith
  rw [div_sub_div _ _ h0.ne' h2.ne', one_mul, mul_one, ← mul_div_assoc, div_le_div_iff₀
    (by positivity) (by positivity)]
  have h7 : Real.log (n : ℝ) * Real.log ((n + 1 : ℕ) : ℝ) ≤ Real.log ((n + 1 : ℕ) : ℝ) ^ 2 := by
    rw [sq]; exact mul_le_mul_of_nonneg_right h1 h2.le
  have h8 : 1 ≤ 2 * (n : ℝ) * (Real.log ((n + 1 : ℕ) : ℝ) - Real.log n) := by
    have := mul_le_mul_of_nonneg_left hd (show (0 : ℝ) ≤ 2 * (n : ℝ) by positivity)
    rwa [show 2 * (n : ℝ) * (1 / (2 * (n : ℝ))) = 1 by field_simp] at this
  nlinarith [mul_pos h0 h2, sq_nonneg (Real.log ((n + 1 : ℕ) : ℝ))]

end MasulloGRH.DP

-- ===== DP2 =====


namespace MasulloGRH.DP

open Filter Topology

/-! ### Partial summation -/

/-- From an asymptotic for the partial sums `∑_{n<N} b_n = r N^{1+w}/(1+w) + O(N e^{-c₁√log N})`
to a uniform Cauchy bound for `∑_{n≤N} b_n/n - r N^w/w`. -/
theorem cauchy_bound (c₁ D A δ : ℝ) (r : ℂ) (N₁ : ℕ) (hc₁ : 0 < c₁) (hD : 0 ≤ D) (hA : 1 ≤ A)
    (hδ : 0 < δ) :
    ∃ Φ : ℕ → ℝ, Tendsto Φ atTop (𝓝 0) ∧ ∃ M₀ : ℕ, ∀ (b : ℕ → ℂ) (w : ℂ),
      w.re ≤ 0 → ‖w‖ ≤ A → ‖1 + w‖ ≤ A → δ ≤ ‖w‖ → 1 / 2 ≤ ‖1 + w‖ →
      (∀ N : ℕ, N₁ ≤ N → ‖(∑ n ∈ Finset.range N, b n) - r * (N : ℂ) ^ (1 + w) / (1 + w)‖ ≤
        D * N * Real.exp (-c₁ * Real.sqrt (Real.log N))) →
      ∀ M : ℕ, M₀ ≤ M → ∀ k : ℕ,
        ‖(∑ n ∈ Finset.Icc 1 (M + k), b n / (n : ℂ) - r * ((M + k : ℕ) : ℂ) ^ w / w) -
          (∑ n ∈ Finset.Icc 1 M, b n / (n : ℂ) - r * (M : ℂ) ^ w / w)‖ ≤ Φ M := by
  set κ : ℝ := 24 / c₁ ^ 4 with hκ
  have hκ0 : 0 < κ := by positivity
  set K : ℝ := 6 * A ^ 2 * (2 + 1 / δ) with hK
  have hK0 : 0 < K := by positivity
  refine ⟨fun M => 4 * D * κ / (Real.log M) ^ 2 + 2 * D * κ / Real.log M + ‖r‖ * K / M, ?_,
    max (max N₁ 3) ⌈4 * A⌉₊, ?_⟩
  · have hlog : Tendsto (fun M : ℕ => Real.log (M : ℝ)) atTop atTop :=
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    have h1 : Tendsto (fun M : ℕ => 4 * D * κ / (Real.log M) ^ 2) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop ((tendsto_pow_atTop two_ne_zero).comp hlog)
    have h2 : Tendsto (fun M : ℕ => 2 * D * κ / Real.log M) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hlog
    have h3 : Tendsto (fun M : ℕ => ‖r‖ * K / (M : ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    simpa using (h1.add h2).add h3
  intro b w hre hwA hw1A hwδ hw1 hB M hM k
  have hMN₁ : N₁ ≤ M := (le_max_left _ _).trans ((le_max_left _ _).trans hM)
  have hM3 : 3 ≤ M := (le_max_right _ _).trans ((le_max_left _ _).trans hM)
  have hMA : 4 * A ≤ (M : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right _ _).trans hM)
  have hw0 : w ≠ 0 := norm_pos_iff.1 (lt_of_lt_of_le hδ hwδ)
  have hw10 : 1 + w ≠ 0 := norm_pos_iff.1 (lt_of_lt_of_le (by norm_num) hw1)
  set E : ℕ → ℂ := fun n => (∑ j ∈ Finset.range n, b j) - r * (n : ℂ) ^ (1 + w) / (1 + w) with hE
  -- bound for `E`
  have hEb : ∀ n : ℕ, M ≤ n → ‖E n‖ ≤ D * n * (κ / (Real.log n) ^ 2) := by
    intro n hn
    refine (hB n (hMN₁.trans hn)).trans ?_
    exact mul_le_mul_of_nonneg_left (eps_le c₁ hc₁ n (by omega)) (by positivity)
  set Yf : ℕ → ℂ := fun N => ∑ n ∈ Finset.Icc 1 N,
    (((n + 1 : ℕ) : ℂ) ^ (1 + w) - (n : ℂ) ^ (1 + w)) / ((1 + w) * (n : ℂ)) - (N : ℂ) ^ w / w
    with hYf
  set Zf : ℕ → ℂ := fun N => ∑ n ∈ Finset.Icc 1 N, (E (n + 1) - E n) / (n : ℂ) with hZf
  set Wf : ℕ → ℂ := fun N => Zf N - E (N + 1) / (N : ℂ) with hWf
  have hb : ∀ n : ℕ, b n = E (n + 1) - E n +
      r * ((((n + 1 : ℕ) : ℂ) ^ (1 + w) - (n : ℂ) ^ (1 + w)) / (1 + w)) := by
    intro n
    simp only [hE, Finset.sum_range_succ]
    ring
  have hX : ∀ N : ℕ, ∑ n ∈ Finset.Icc 1 N, b n / (n : ℂ) - r * (N : ℂ) ^ w / w =
      Wf N + E (N + 1) / (N : ℂ) + r * Yf N := by
    intro N
    have hs : ∑ n ∈ Finset.Icc 1 N, b n / (n : ℂ) = Zf N + r * ∑ n ∈ Finset.Icc 1 N,
        (((n + 1 : ℕ) : ℂ) ^ (1 + w) - (n : ℂ) ^ (1 + w)) / ((1 + w) * (n : ℂ)) := by
      rw [hZf, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun n hn => ?_
      have hn0 : (n : ℂ) ≠ 0 := by
        have := (Finset.mem_Icc.1 hn).1
        exact_mod_cast (by omega : n ≠ 0)
      conv_lhs => rw [hb n]
      field_simp
    rw [hs, hWf, hYf]
    ring
  -- increments of `Wf`
  have hWinc : ∀ n : ℕ, M ≤ n →
      ‖Wf (n + 1) - Wf n‖ ≤ 2 * D * κ / Real.log n - 2 * D * κ / Real.log ((n + 1 : ℕ) : ℝ) := by
    intro n hn
    have hn2 : 2 ≤ n := by omega
    have hnR : (0 : ℝ) < (n : ℝ) := by positivity
    have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
    have hn1 : ((n + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    have e : Wf (n + 1) - Wf n = E (n + 1) * (1 / (n : ℂ) - 1 / ((n + 1 : ℕ) : ℂ)) := by
      simp only [hWf, hZf]
      rw [Finset.sum_Icc_succ_top (by omega)]
      field_simp
      ring
    have e2 : ‖(1 / (n : ℂ) - 1 / ((n + 1 : ℕ) : ℂ))‖ = 1 / ((n : ℝ) * ((n + 1 : ℕ) : ℝ)) := by
      have : (1 / (n : ℂ) - 1 / ((n + 1 : ℕ) : ℂ)) = ((1 / ((n : ℝ) * ((n + 1 : ℕ) : ℝ)) : ℝ) : ℂ) := by
        push_cast; field_simp; ring
      rw [this, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    rw [e, norm_mul, e2]
    have h1 := hEb (n + 1) (by omega)
    have hlog1 : 0 < Real.log ((n + 1 : ℕ) : ℝ) :=
      Real.log_pos (by push_cast; linarith [show (2 : ℝ) ≤ n by exact_mod_cast hn2])
    have h2 := log_tele n hn2
    calc ‖E (n + 1)‖ * (1 / ((n : ℝ) * ((n + 1 : ℕ) : ℝ)))
        ≤ D * ((n + 1 : ℕ) : ℝ) * (κ / (Real.log ((n + 1 : ℕ) : ℝ)) ^ 2) *
            (1 / ((n : ℝ) * ((n + 1 : ℕ) : ℝ))) :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = D * κ * (1 / ((n : ℝ) * (Real.log ((n + 1 : ℕ) : ℝ)) ^ 2)) := by
          have : (((n + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
          field_simp
      _ ≤ D * κ * (2 * (1 / Real.log n - 1 / Real.log ((n + 1 : ℕ) : ℝ))) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = _ := by ring
  -- increments of `Yf`
  have hYinc : ∀ n : ℕ, M ≤ n → ‖Yf (n + 1) - Yf n‖ ≤ K / (n : ℝ) - K / ((n + 1 : ℕ) : ℝ) := by
    intro n hn
    have hn1 : 1 ≤ n := by omega
    have hnR : (0 : ℝ) < (n : ℝ) := by positivity
    have e : Yf (n + 1) - Yf n =
        (((n + 1 + 1 : ℕ) : ℂ) ^ (1 + w) - ((n + 1 : ℕ) : ℂ) ^ (1 + w)) /
          ((1 + w) * ((n + 1 : ℕ) : ℂ)) - (((n + 1 : ℕ) : ℂ) ^ w - (n : ℂ) ^ w) / w := by
      simp only [hYf]
      rw [Finset.sum_Icc_succ_top (by omega)]
      ring
    rw [e]
    have hA' : 4 * A ≤ ((n + 1 : ℕ) : ℝ) := by
      push_cast; linarith [show (M : ℝ) ≤ n by exact_mod_cast hn]
    refine (U_bound w A δ hA hwA hw1A hδ hwδ hw1 hre n hn1 hA').trans ?_
    rw [← hK, div_sub_div _ _ hnR.ne' (by positivity), div_le_div_iff₀ (by positivity)
      (by positivity)]
    push_cast
    nlinarith [hK0, hnR]
  have t1 := tele Wf (fun n => 2 * D * κ / Real.log n) M hWinc k
  have t2 := tele Yf (fun n => K / (n : ℝ)) M hYinc k
  have hMR : (3 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM3
  have hlogM : 0 < Real.log (M : ℝ) := Real.log_pos (by linarith)
  -- boundary terms
  have hbdry : ∀ N : ℕ, M ≤ N → ‖E (N + 1) / (N : ℂ)‖ ≤ 2 * D * κ / (Real.log M) ^ 2 := by
    intro N hN
    have hNR : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hM3.trans hN
    have h1 := hEb (N + 1) (by omega)
    have hlogle : Real.log (M : ℝ) ≤ Real.log ((N + 1 : ℕ) : ℝ) :=
      Real.log_le_log (by linarith) (by push_cast; linarith [show (M : ℝ) ≤ N by exact_mod_cast hN])
    have h3 : κ / (Real.log ((N + 1 : ℕ) : ℝ)) ^ 2 ≤ κ / (Real.log M) ^ 2 :=
      div_le_div_of_nonneg_left hκ0.le (by positivity) (pow_le_pow_left₀ hlogM.le hlogle 2)
    rw [norm_div, Complex.norm_natCast, div_le_iff₀ (by linarith)]
    calc ‖E (N + 1)‖ ≤ D * ((N + 1 : ℕ) : ℝ) * (κ / (Real.log ((N + 1 : ℕ) : ℝ)) ^ 2) := h1
      _ ≤ D * (2 * (N : ℝ)) * (κ / (Real.log M) ^ 2) := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left (by push_cast; linarith) hD) h3
            (by positivity) (by positivity)
      _ = 2 * D * κ / (Real.log M) ^ 2 * (N : ℝ) := by ring
  have b1 := hbdry (M + k) (Nat.le_add_right _ _)
  have b2 := hbdry M le_rfl
  have hT1 : 0 ≤ 2 * D * κ / Real.log ((M + k : ℕ) : ℝ) :=
    div_nonneg (by positivity) (Real.log_natCast_nonneg _)
  have hT2 : 0 ≤ K / ((M + k : ℕ) : ℝ) := by positivity
  rw [hX (M + k), hX M]
  calc ‖Wf (M + k) + E (M + k + 1) / ((M + k : ℕ) : ℂ) + r * Yf (M + k) -
        (Wf M + E (M + 1) / (M : ℂ) + r * Yf M)‖
      = ‖(Wf (M + k) - Wf M) + E (M + k + 1) / ((M + k : ℕ) : ℂ) - E (M + 1) / (M : ℂ) +
          r * (Yf (M + k) - Yf M)‖ := by congr 1; ring
    _ ≤ ‖Wf (M + k) - Wf M‖ + ‖E (M + k + 1) / ((M + k : ℕ) : ℂ)‖ + ‖E (M + 1) / (M : ℂ)‖ +
          ‖r‖ * ‖Yf (M + k) - Yf M‖ := by
        refine (norm_add_le _ _).trans (add_le_add ((norm_sub_le _ _).trans
          (add_le_add (norm_add_le _ _) le_rfl)) (norm_mul _ _).le)
    _ ≤ 2 * D * κ / Real.log M + 2 * D * κ / (Real.log M) ^ 2 + 2 * D * κ / (Real.log M) ^ 2 +
          ‖r‖ * (K / M) := by
        have t1' : ‖Wf (M + k) - Wf M‖ ≤ 2 * D * κ / Real.log M := by linarith
        have t2' : ‖Yf (M + k) - Yf M‖ ≤ K / M := by linarith
        have := mul_le_mul_of_nonneg_left t2' (norm_nonneg r)
        linarith
    _ = 4 * D * κ / (Real.log M) ^ 2 + 2 * D * κ / Real.log M + ‖r‖ * K / M := by ring

end MasulloGRH.DP

-- ===== DP3 =====


namespace MasulloGRH.DP

open Filter Topology

/-! ### Applying Perron's formula with a shift -/

/-- A point of Davenport's region with parameter `q ≥ R + 2`, shifted by `s - 1` with
`Re s ≥ 1` and `|Im s| ≤ R`, lies in the region `σ ≥ 1 - c / log (|t| + 3)`; moreover the
logarithms compare. -/
lemma region_shift (c R : ℝ) (hc : 0 < c) (q : ℕ) (hq : R + 2 ≤ (q : ℝ)) (hR : 0 ≤ R)
    (s z : ℂ) (hs : 1 ≤ s.re) (hsR : |s.im| ≤ R) :
    0 < Real.log (|(z + (s - 1)).im| + 3) ∧
    Real.log (|(z + (s - 1)).im| + 3) ≤ Real.log ((q : ℝ) * (|z.im| + 2)) ∧
    (SWPort.Davenport.InRegion c q z →
      1 - c / Real.log (|(z + (s - 1)).im| + 3) ≤ (z + (s - 1)).re) := by
  have him : (z + (s - 1)).im = z.im + s.im := by simp
  have hre : (z + (s - 1)).re = z.re + s.re - 1 := by simp; ring
  have h3 : (3 : ℝ) ≤ |(z + (s - 1)).im| + 3 := by linarith [abs_nonneg (z + (s - 1)).im]
  have hpos : 0 < Real.log (|(z + (s - 1)).im| + 3) := Real.log_pos (by linarith)
  have hle : |(z + (s - 1)).im| + 3 ≤ (q : ℝ) * (|z.im| + 2) := by
    rw [him]
    have h1 := abs_add_le z.im s.im
    have h2 : (R + 2) * (|z.im| + 2) ≤ (q : ℝ) * (|z.im| + 2) :=
      mul_le_mul_of_nonneg_right hq (by positivity)
    nlinarith [abs_nonneg z.im]
  have hlog := Real.log_le_log (by linarith) hle
  refine ⟨hpos, hlog, fun hz => ?_⟩
  unfold SWPort.Davenport.InRegion SWPort.Davenport.regionBoundary at hz
  have h4 : c / Real.log ((q : ℝ) * (|z.im| + 2)) ≤ c / Real.log (|(z + (s - 1)).im| + 3) :=
    div_le_div_of_nonneg_left hc.le hpos hlog
  rw [hre]
  linarith

theorem perron_uniform (a : ℕ → ℂ) (G : ℂ → ℂ) (M c C : ℝ) (r : ℂ) (t₀ : ℝ) (hc : 0 < c)
    (ha : ∀ n : ℕ, ‖a n‖ ≤ M * ArithmeticFunction.vonMangoldt n)
    (hG : ∀ s : ℂ, 1 < s.re → G s = LSeries a s)
    (han : ∀ s : ℂ, 1 - c / Real.log (|s.im| + 3) ≤ s.re → s ≠ 1 + t₀ * Complex.I →
      AnalyticAt ℂ G s)
    (hbd : ∀ s : ℂ, 1 - c / Real.log (|s.im| + 3) ≤ s.re → s ≠ 1 + t₀ * Complex.I →
      ‖G s - r / (s - (1 + t₀ * Complex.I))‖ ≤ C * Real.log (|s.im| + 3) ^ 2)
    (R : ℝ) (hR : 0 ≤ R) :
    ∃ c₁ D : ℝ, ∃ N₁ : ℕ, 0 < c₁ ∧ 0 ≤ D ∧ ∀ s : ℂ, 1 ≤ s.re → s.re ≤ 3 / 2 → |s.im| ≤ R →
      s ≠ 1 + t₀ * Complex.I → ∀ N : ℕ, N₁ ≤ N →
        ‖(∑ n ∈ Finset.range N, a n * (n : ℂ) ^ (-(s - 1))) -
            r * (N : ℂ) ^ (1 + (1 + t₀ * Complex.I - s)) / (1 + (1 + t₀ * Complex.I - s))‖ ≤
          D * N * Real.exp (-c₁ * Real.sqrt (Real.log N)) := by
  set Mp : ℝ := max M 1 with hMp
  have hMp1 : 1 ≤ Mp := le_max_right _ _
  have hMp0 : 0 < Mp := by linarith
  have hMpC : (Mp : ℂ) ≠ 0 := by exact_mod_cast hMp0.ne'
  set q : ℕ := ⌈R⌉₊ + 2 with hq
  have hqR : R + 2 ≤ (q : ℝ) := by rw [hq]; push_cast; linarith [Nat.le_ceil R]
  haveI : NeZero q := ⟨by omega⟩
  set C₀ : ℝ := |C| + ‖r‖ + 1 with hC₀
  have hC₀pos : 0 < C₀ := by positivity
  obtain ⟨c₁, c₂, C', hc₁, hc₂, hC', hP⟩ := SWPort.Davenport.perron_of_region_bound c C₀ hc hC₀pos
  have hev : ∀ᶠ N : ℕ in atTop, (q : ℝ) ≤ Real.exp (c₂ * Real.sqrt (Real.log N)) := by
    have ht : Tendsto (fun N : ℕ => Real.exp (c₂ * Real.sqrt (Real.log N))) atTop atTop :=
      Real.tendsto_exp_atTop.comp ((Real.tendsto_sqrt_atTop.comp
        (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).const_mul_atTop hc₂)
    exact ht.eventually_ge_atTop _
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 hev
  refine ⟨c₁, Mp * C', max N₀ 2, hc₁, by positivity, ?_⟩
  intro s hs1 hs2 hsR hsne N hN
  have hNN₀ : N₀ ≤ N := (le_max_left _ _).trans hN
  have hN2 : 2 ≤ N := (le_max_right _ _).trans hN
  have ha0 : a 0 = 0 := by
    have := ha 0
    rw [ArithmeticFunction.map_zero, mul_zero] at this
    exact norm_le_zero_iff.1 this
  have key := hP q (fun n => (Mp : ℂ)⁻¹ * (a n * (n : ℂ) ^ (-(s - 1))))
    (fun z => (Mp : ℂ)⁻¹ * G (z + (s - 1))) {1 + t₀ * Complex.I - (s - 1)}
    (fun _ => (Mp : ℂ)⁻¹ * r) ?_ ?_ ?_ ?_ ?_ ?_ N hN2 (hN₀ N hNN₀)
  · rw [← Finset.mul_sum, Finset.sum_singleton] at key
    have e : (Mp : ℂ)⁻¹ * ∑ n ∈ Finset.range N, a n * (n : ℂ) ^ (-(s - 1)) -
        (Mp : ℂ)⁻¹ * r * (N : ℂ) ^ (1 + t₀ * Complex.I - (s - 1)) / (1 + t₀ * Complex.I - (s - 1)) =
        (Mp : ℂ)⁻¹ * ((∑ n ∈ Finset.range N, a n * (n : ℂ) ^ (-(s - 1))) -
          r * (N : ℂ) ^ (1 + (1 + t₀ * Complex.I - s)) / (1 + (1 + t₀ * Complex.I - s))) := by
      rw [show 1 + t₀ * Complex.I - (s - 1) = 1 + (1 + t₀ * Complex.I - s) by ring]
      ring
    rw [e, norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hMp0.le,
      inv_mul_le_iff₀ hMp0] at key
    calc _ ≤ Mp * (C' * N * Real.exp (-c₁ * Real.sqrt (Real.log N))) := key
      _ = _ := by ring
  · -- coefficient bound
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [ha0]; simp
    · have h1 : ‖(n : ℂ) ^ (-(s - 1))‖ ≤ 1 := by
        rw [Complex.norm_natCast_cpow_of_pos hn]
        refine Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hn) ?_
        simp; linarith
      have hΛ : 0 ≤ ArithmeticFunction.vonMangoldt n := ArithmeticFunction.vonMangoldt_nonneg
      rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hMp0.le, norm_mul,
        inv_mul_le_iff₀ hMp0]
      calc ‖a n‖ * ‖(n : ℂ) ^ (-(s - 1))‖ ≤ (M * ArithmeticFunction.vonMangoldt n) * 1 :=
            mul_le_mul (ha n) h1 (norm_nonneg _) ((norm_nonneg _).trans (ha n))
        _ ≤ Mp * ArithmeticFunction.vonMangoldt n := by
            rw [mul_one]; exact mul_le_mul_of_nonneg_right (le_max_left _ _) hΛ
  · -- Dirichlet series
    intro z hz
    have hre : 1 < (z + (s - 1)).re := by simp; linarith
    show (Mp : ℂ)⁻¹ * G (z + (s - 1)) = _
    rw [hG _ hre]
    unfold LSeries
    rw [← tsum_mul_left]
    refine tsum_congr fun n => ?_
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
      rw [LSeries.term_def, LSeries.term_def, if_neg hn.ne', if_neg hn.ne', Complex.cpow_add _ _ hn0,
        Complex.cpow_neg]
      have h1 : (n : ℂ) ^ z ≠ 0 := by
        rw [Complex.cpow_def_of_ne_zero hn0]; exact Complex.exp_ne_zero _
      have h2 : (n : ℂ) ^ (s - 1) ≠ 0 := by
        rw [Complex.cpow_def_of_ne_zero hn0]; exact Complex.exp_ne_zero _
      field_simp
  · -- analyticity
    intro z hz
    obtain ⟨⟨hzr, -⟩, hzP⟩ := hz
    have hne : z + (s - 1) ≠ 1 + t₀ * Complex.I := by
      intro h
      apply hzP
      rw [Finset.coe_singleton, Set.mem_singleton_iff]
      linear_combination h
    have hreg := (region_shift c R hc q hqR hR s z hs1 hsR).2.2 hzr
    have h1 : AnalyticAt ℂ (fun z : ℂ => G (z + (s - 1))) z :=
      (han _ hreg hne).comp (f := fun z : ℂ => z + (s - 1)) (analyticAt_id.add analyticAt_const)
    exact analyticAt_const.mul h1
  · -- location of the pole
    intro p hp
    rw [Finset.mem_singleton] at hp
    have hre : p.re = 2 - s.re := by rw [hp]; simp; ring
    rw [hre]
    constructor <;> linarith
  · -- size of the residue
    rw [Finset.sum_singleton, norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hMp0.le]
    have h1 : Mp⁻¹ * ‖r‖ ≤ ‖r‖ := by
      rw [inv_mul_le_iff₀ hMp0]; exact le_mul_of_one_le_left (norm_nonneg _) hMp1
    have h2 : (1 : ℝ) ≤ Real.log (2 * (q : ℝ)) := by
      rw [Real.le_log_iff_exp_le (by positivity)]
      have := Real.exp_one_lt_d9
      have hq2 : (2 : ℝ) ≤ (q : ℝ) := by linarith
      linarith
    have h3 : ‖r‖ ≤ C₀ := by rw [hC₀]; linarith [abs_nonneg C]
    calc Mp⁻¹ * ‖r‖ ≤ C₀ * 1 := by linarith
      _ ≤ C₀ * Real.log (2 * (q : ℝ)) := mul_le_mul_of_nonneg_left h2 hC₀pos.le
  · -- bound in the region
    intro z hzr _ hzP
    rw [Finset.sum_singleton]
    obtain ⟨hpos, hlog, hreg⟩ := region_shift c R hc q hqR hR s z hs1 hsR
    have hne : z + (s - 1) ≠ 1 + t₀ * Complex.I := by
      intro h
      apply hzP
      rw [Finset.mem_singleton]
      linear_combination h
    have hb := hbd _ (hreg hzr) hne
    have e : (Mp : ℂ)⁻¹ * G (z + (s - 1)) - (Mp : ℂ)⁻¹ * r / (z - (1 + t₀ * Complex.I - (s - 1))) =
        (Mp : ℂ)⁻¹ * (G (z + (s - 1)) - r / (z + (s - 1) - (1 + t₀ * Complex.I))) := by
      rw [show z - (1 + t₀ * Complex.I - (s - 1)) = z + (s - 1) - (1 + t₀ * Complex.I) by ring]
      ring
    rw [e, norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hMp0.le,
      inv_mul_le_iff₀ hMp0]
    have h5 : |C| ≤ C₀ := by rw [hC₀]; linarith [norm_nonneg r]
    have hL : 0 ≤ Real.log ((q : ℝ) * (|z.im| + 2)) ^ 2 := by positivity
    calc ‖G (z + (s - 1)) - r / (z + (s - 1) - (1 + t₀ * Complex.I))‖
        ≤ C * Real.log (|(z + (s - 1)).im| + 3) ^ 2 := hb
      _ ≤ |C| * Real.log ((q : ℝ) * (|z.im| + 2)) ^ 2 :=
          mul_le_mul (le_abs_self C) (pow_le_pow_left₀ hpos.le hlog 2) (by positivity)
            (abs_nonneg _)
      _ ≤ C₀ * Real.log ((q : ℝ) * (|z.im| + 2)) ^ 2 := mul_le_mul_of_nonneg_right h5 hL
      _ ≤ Mp * (C₀ * Real.log ((q : ℝ) * (|z.im| + 2)) ^ 2) :=
          le_mul_of_one_le_left (by positivity) hMp1

end MasulloGRH.DP

-- ===== DP4 =====


namespace MasulloGRH.DP

open Filter Topology

lemma sum_Icc_eq_range (g : ℕ → ℂ) (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, g n = ∑ n ∈ Finset.range (N + 1), if n = 0 then 0 else g n := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ (n := N + 1),
      if_neg (by omega)]

lemma lseriesSummable_of_le (a : ℕ → ℂ) (M : ℝ)
    (ha : ∀ n : ℕ, ‖a n‖ ≤ M * ArithmeticFunction.vonMangoldt n) {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable a s := by
  have h := ((ArithmeticFunction.LSeriesSummable_vonMangoldt hs).norm).mul_left |M|
  refine Summable.of_norm_bounded h fun n => ?_
  rw [LSeries.norm_term_eq, LSeries.norm_term_eq]
  split_ifs with hn
  · simp
  · have hΛ : 0 ≤ ArithmeticFunction.vonMangoldt n := ArithmeticFunction.vonMangoldt_nonneg
    rw [Complex.norm_real, Real.norm_of_nonneg hΛ, ← mul_div_assoc]
    refine div_le_div_of_nonneg_right ((ha n).trans ?_) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    exact mul_le_mul_of_nonneg_right (le_abs_self M) hΛ

theorem main (a : ℕ → ℂ) (G : ℂ → ℂ) (M c C : ℝ) (r : ℂ) (t₀ : ℝ) (hc : 0 < c)
    (ha : ∀ n : ℕ, ‖a n‖ ≤ M * ArithmeticFunction.vonMangoldt n)
    (hG : ∀ s : ℂ, 1 < s.re → G s = LSeries a s)
    (han : ∀ s : ℂ, 1 - c / Real.log (|s.im| + 3) ≤ s.re → s ≠ 1 + t₀ * Complex.I →
      AnalyticAt ℂ G s)
    (hbd : ∀ s : ℂ, 1 - c / Real.log (|s.im| + 3) ≤ s.re → s ≠ 1 + t₀ * Complex.I →
      ‖G s - r / (s - (1 + t₀ * Complex.I))‖ ≤ C * Real.log (|s.im| + 3) ^ 2) :
    TendstoLocallyUniformlyOn
      (fun (N : ℕ) (s : ℂ) =>
        ∑ n ∈ Finset.Icc 1 N, a n * (n : ℂ) ^ (-s) -
          r * (N : ℂ) ^ (1 + t₀ * Complex.I - s) / (1 + t₀ * Complex.I - s))
      G Filter.atTop {s : ℂ | s.re = 1 ∧ s.im ≠ t₀} := by
  intro u hu s₀ hs₀
  obtain ⟨hs₀re, hs₀im⟩ := hs₀
  set η : ℝ := |s₀.im - t₀| / 2 with hηdef
  have hη : 0 < η := half_pos (abs_pos.2 (sub_ne_zero.2 hs₀im))
  set Q : Set ℂ := {s : ℂ | 1 ≤ s.re ∧ s.re ≤ 3 / 2 ∧ |s.im - s₀.im| ≤ η} with hQ
  have hQim : ∀ s ∈ Q, η ≤ |s.im - t₀| := by
    intro s hs
    have h1 := abs_sub_le s₀.im s.im t₀
    have h2 : |s₀.im - s.im| ≤ η := by rw [abs_sub_comm]; exact hs.2.2
    have h3 : |s₀.im - t₀| = 2 * η := by rw [hηdef]; ring
    linarith
  have hQne : ∀ s ∈ Q, s ≠ 1 + t₀ * Complex.I := by
    intro s hs h
    have h1 := hQim s hs
    rw [h] at h1
    simp at h1
    linarith
  set R : ℝ := |s₀.im| + η with hRdef
  have hR0 : 0 ≤ R := by positivity
  have hQR : ∀ s ∈ Q, |s.im| ≤ R := by
    intro s hs
    have h1 := abs_add_le (s.im - s₀.im) s₀.im
    rw [sub_add_cancel] at h1
    linarith [hs.2.2]
  obtain ⟨c₁, D, N₁, hc₁, hD, hPer⟩ := perron_uniform a G M c C r t₀ hc ha hG han hbd R hR0
  set A : ℝ := |t₀| + R + 2 with hAdef
  have hA1 : 1 ≤ A := by rw [hAdef]; linarith [abs_nonneg t₀]
  obtain ⟨Φ, hΦ, M₀, hCB⟩ := cauchy_bound c₁ D A η r N₁ hc₁ hD hA1 hη
  set X : ℕ → ℂ → ℂ := fun N s => ∑ n ∈ Finset.Icc 1 N, a n * (n : ℂ) ^ (-s) -
    r * (N : ℂ) ^ (1 + t₀ * Complex.I - s) / (1 + t₀ * Complex.I - s) with hX
  -- the exponent `w = p - s` on `Q`
  have hw : ∀ s ∈ Q, (1 + t₀ * Complex.I - s).re ≤ 0 ∧ ‖1 + t₀ * Complex.I - s‖ ≤ A ∧
      ‖1 + (1 + t₀ * Complex.I - s)‖ ≤ A ∧ η ≤ ‖1 + t₀ * Complex.I - s‖ ∧
      1 / 2 ≤ ‖1 + (1 + t₀ * Complex.I - s)‖ := by
    intro s hs
    have hre : (1 + t₀ * Complex.I - s).re = 1 - s.re := by simp
    have him : (1 + t₀ * Complex.I - s).im = t₀ - s.im := by simp
    have hn1 : ‖1 + t₀ * Complex.I - s‖ ≤ A - 1 := by
      refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
      rw [hre, him, hAdef]
      have h1 : |1 - s.re| ≤ 1 / 2 := by rw [abs_le]; constructor <;> linarith [hs.1, hs.2.1]
      have h2 : |t₀ - s.im| ≤ |t₀| + |s.im| := abs_sub _ _
      linarith [hQR s hs]
    refine ⟨by rw [hre]; linarith [hs.1], by linarith, ?_, ?_, ?_⟩
    · refine (norm_add_le _ _).trans ?_
      rw [norm_one]; linarith
    · have := Complex.abs_im_le_norm (1 + t₀ * Complex.I - s)
      rw [him, abs_sub_comm] at this
      exact (hQim s hs).trans this
    · have := Complex.re_le_norm (1 + (1 + t₀ * Complex.I - s))
      rw [Complex.add_re, hre, Complex.one_re] at this
      linarith [hs.2.1]
  -- uniform Cauchy property on `Q`
  have hUC : UniformCauchySeqOn X atTop Q := by
    rw [Metric.uniformCauchySeqOn_iff]
    intro ε hε
    obtain ⟨M₁, hM₁⟩ := eventually_atTop.1 (hΦ.eventually (gt_mem_nhds (half_pos hε)))
    refine ⟨max M₀ M₁, fun m hm n hn s hs => ?_⟩
    obtain ⟨hw1, hw2, hw3, hw4, hw5⟩ := hw s hs
    have key : ∀ k : ℕ, ‖X (max M₀ M₁ + k) s - X (max M₀ M₁) s‖ ≤ Φ (max M₀ M₁) := by
      intro k
      have h := hCB (fun n => a n * (n : ℂ) ^ (-(s - 1))) (1 + t₀ * Complex.I - s) hw1 hw2 hw3 hw4
        hw5 (fun N hN => hPer s hs.1 hs.2.1 (hQR s hs) (hQne s hs) N hN) (max M₀ M₁)
        (le_max_left _ _) k
      have e : ∀ N : ℕ, ∑ n ∈ Finset.Icc 1 N, a n * (n : ℂ) ^ (-(s - 1)) / (n : ℂ) =
          ∑ n ∈ Finset.Icc 1 N, a n * (n : ℂ) ^ (-s) := by
        intro N
        refine Finset.sum_congr rfl fun n hn => ?_
        have hn0 : (n : ℂ) ≠ 0 := by
          have := (Finset.mem_Icc.1 hn).1
          exact_mod_cast (by omega : n ≠ 0)
        rw [show -(s - 1) = -s + 1 by ring, Complex.cpow_add _ _ hn0, Complex.cpow_one]
        field_simp
      rw [e, e] at h
      exact h
    obtain ⟨k₁, rfl⟩ := Nat.exists_eq_add_of_le hm
    obtain ⟨k₂, rfl⟩ := Nat.exists_eq_add_of_le hn
    have hΦlt := hM₁ (max M₀ M₁) (le_max_right _ _)
    calc dist (X (max M₀ M₁ + k₁) s) (X (max M₀ M₁ + k₂) s)
        ≤ dist (X (max M₀ M₁ + k₁) s) (X (max M₀ M₁) s) +
            dist (X (max M₀ M₁ + k₂) s) (X (max M₀ M₁) s) := dist_triangle_right _ _ _
      _ < ε := by
          rw [dist_eq_norm, dist_eq_norm]
          have := key k₁
          have := key k₂
          linarith
  set ℓ : ℂ → ℂ := fun s => limUnder atTop (fun N : ℕ => X N s) with hℓ
  have hT : TendstoUniformlyOn X ℓ atTop Q :=
    hUC.tendstoUniformlyOn_of_tendsto fun s hs => CauchySeq.tendsto_limUnder (hUC.cauchy_map hs)
  have hXc : ∀ N : ℕ, ContinuousOn (X N) Q := by
    intro N
    refine ContinuousOn.sub (continuousOn_finsetSum _ fun n hn => ?_) ?_
    · have hn0 : (n : ℂ) ≠ 0 := by
        have := (Finset.mem_Icc.1 hn).1
        exact_mod_cast (by omega : n ≠ 0)
      exact (continuous_const.mul (continuous_neg.const_cpow (Or.inl hn0))).continuousOn
    · have hsub : ContinuousOn (fun s : ℂ => 1 + t₀ * Complex.I - s) Q :=
        (continuous_const.sub continuous_id).continuousOn
      refine ContinuousOn.div (continuousOn_const.mul (hsub.const_cpow (Or.inr fun s hs => ?_)))
        hsub (fun s hs => ?_)
      · exact sub_ne_zero.2 (hQne s hs).symm
      · exact sub_ne_zero.2 (hQne s hs).symm
  have hℓc : ContinuousOn ℓ Q := hT.continuousOn (Frequently.of_forall hXc)
  -- the limit on `Re s > 1`
  have hℓG : ∀ s ∈ Q, 1 < s.re → ℓ s = G s := by
    intro s hs hre
    refine tendsto_nhds_unique (hT.tendsto_at hs) ?_
    have hsum := (lseriesSummable_of_le a M ha hre).hasSum.tendsto_sum_nat.comp
      (tendsto_add_atTop_nat 1)
    have h1 : Tendsto (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, a n * (n : ℂ) ^ (-s)) atTop (𝓝 (G s)) := by
      rw [hG s hre]
      refine hsum.congr fun N => ?_
      rw [sum_Icc_eq_range]
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [LSeries.term_def, Complex.cpow_neg, div_eq_mul_inv]
    have h2 : Tendsto (fun N : ℕ => (N : ℂ) ^ (1 + t₀ * Complex.I - s)) atTop (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      have h3 : Tendsto (fun N : ℕ => (N : ℝ) ^ (-(s.re - 1))) atTop (𝓝 0) :=
        (tendsto_rpow_neg_atTop (by linarith)).comp tendsto_natCast_atTop_atTop
      refine h3.congr' ?_
      filter_upwards [eventually_ge_atTop 1] with N hN
      rw [Complex.norm_natCast_cpow_of_pos (by omega)]
      congr 1
      simp
    have h4 := h1.sub ((h2.const_mul r).div_const (1 + t₀ * Complex.I - s))
    simp only [mul_zero, zero_div, sub_zero] at h4
    refine h4.congr fun N => ?_
    simp only [hX, mul_div_assoc]
  -- the limit on the line, by continuity
  have hline : ∀ s ∈ Q, s.re = 1 → ℓ s = G s := by
    intro s hs hre
    have hmem : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), s + (ε : ℂ) ∈ Q ∧ 1 < (s + (ε : ℂ)).re := by
      filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 2 by norm_num)] with ε hε
      refine ⟨⟨?_, ?_, ?_⟩, ?_⟩ <;> simp <;> linarith [hε.1, hε.2, hs.2.2]
    have hto : Tendsto (fun ε : ℝ => s + (ε : ℂ)) (𝓝[>] (0 : ℝ)) (𝓝 s) := by
      have : Tendsto (fun ε : ℝ => s + (ε : ℂ)) (𝓝 (0 : ℝ)) (𝓝 (s + ((0 : ℝ) : ℂ))) :=
        (continuous_const.add Complex.continuous_ofReal).tendsto 0
      rw [Complex.ofReal_zero, add_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    have hpath : Tendsto (fun ε : ℝ => s + (ε : ℂ)) (𝓝[>] (0 : ℝ)) (𝓝[Q] s) :=
      tendsto_nhdsWithin_iff.2 ⟨hto, hmem.mono fun ε h => h.1⟩
    have h1 : Tendsto (fun ε : ℝ => ℓ (s + (ε : ℂ))) (𝓝[>] (0 : ℝ)) (𝓝 (ℓ s)) :=
      (hℓc s hs).tendsto.comp hpath
    have hreg : 1 - c / Real.log (|s.im| + 3) ≤ s.re := by
      have : 0 ≤ c / Real.log (|s.im| + 3) :=
        div_nonneg hc.le (Real.log_nonneg (by linarith [abs_nonneg s.im]))
      linarith
    have h2 : Tendsto (fun ε : ℝ => G (s + (ε : ℂ))) (𝓝[>] (0 : ℝ)) (𝓝 (G s)) :=
      (han s hreg (hQne s hs)).continuousAt.tendsto.comp hto
    have h3 : (fun ε : ℝ => ℓ (s + (ε : ℂ))) =ᶠ[𝓝[>] (0 : ℝ)] fun ε => G (s + (ε : ℂ)) :=
      hmem.mono fun ε h => hℓG _ h.1 h.2
    exact tendsto_nhds_unique (h1.congr' h3) h2
  refine ⟨Q ∩ {s : ℂ | s.re = 1 ∧ s.im ≠ t₀}, inter_mem ?_ self_mem_nhdsWithin, ?_⟩
  · refine mem_nhdsWithin.2 ⟨{s : ℂ | |s.im - s₀.im| < η}, ?_, ?_, ?_⟩
    · exact isOpen_lt (by fun_prop) continuous_const
    · simp [hη]
    · rintro s ⟨h1, h2⟩
      exact ⟨h2.1.ge, by rw [h2.1]; norm_num, le_of_lt h1⟩
  · filter_upwards [hT u hu] with N hN y hy
    rw [← hline y hy.1 hy.2.1]
    exact hN y hy.1

end MasulloGRH.DP

theorem solution
    (a : ℕ → ℂ) (G : ℂ → ℂ) (M c C : ℝ) (r : ℂ) (t₀ : ℝ) (hc : 0 < c)
    (ha : ∀ n : ℕ, ‖a n‖ ≤ M * ArithmeticFunction.vonMangoldt n)
    (hG : ∀ s : ℂ, 1 < s.re → G s = LSeries a s)
    (han : ∀ s : ℂ, 1 - c / Real.log (|s.im| + 3) ≤ s.re → s ≠ 1 + t₀ * Complex.I →
      AnalyticAt ℂ G s)
    (hbd : ∀ s : ℂ, 1 - c / Real.log (|s.im| + 3) ≤ s.re → s ≠ 1 + t₀ * Complex.I →
      ‖G s - r / (s - (1 + t₀ * Complex.I))‖ ≤ C * Real.log (|s.im| + 3) ^ 2) :
    TendstoLocallyUniformlyOn
      (fun (N : ℕ) (s : ℂ) =>
        ∑ n ∈ Finset.Icc 1 N, a n * (n : ℂ) ^ (-s) -
          r * (N : ℂ) ^ (1 + t₀ * Complex.I - s) / (1 + t₀ * Complex.I - s))
      G Filter.atTop {s : ℂ | s.re = 1 ∧ s.im ≠ t₀} :=
  MasulloGRH.DP.main a G M c C r t₀ hc ha hG han hbd

