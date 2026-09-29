-- Prove2me | solution 1 for InertialFB.IFB.lemma5_real_sequences
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-28T00:10:14.917853+00:00
-- url     : https://prove2.me/submissions/493c2637-b1dd-4e24-9a12-0d4f5b77fdaf

import Mathlib

theorem solution (a b ε : ℕ → ℝ) (θ : ℝ) (k₀ : ℕ) (hk₀ : 1 ≤ k₀)
    (hε : Summable ε)
    (h₁ : ∀ k : ℕ, k₀ ≤ k → a k - a (k - 1) ≤ θ + ε k)
    (h₂ : ∀ k : ℕ, k₀ ≤ k → b (k + 1) - b k ≤ a k)
    (h₃ : ∀ k : ℕ, k₀ ≤ k → 0 ≤ b k) :
    0 ≤ θ := by
  by_contra hθ
  push_neg at hθ
  set c : ℝ := -θ / 2 with hc
  have hcpos : 0 < c := by rw [hc]; linarith
  -- the summable sequence tends to zero, so eventually  θ + ε k ≤ θ/2 = -c
  have hε0 : Filter.Tendsto ε Filter.atTop (nhds 0) := hε.tendsto_atTop_zero
  have hev : ∀ᶠ k in Filter.atTop, ε k < c := by
    have := hε0.eventually (eventually_lt_nhds hcpos)
    exact this
  obtain ⟨K0, hK0⟩ := Filter.eventually_atTop.mp hev
  set K : ℕ := max k₀ K0 with hK
  have hKk₀ : k₀ ≤ K := le_max_left _ _
  have hKK0 : K0 ≤ K := le_max_right _ _
  have hstep : ∀ k : ℕ, K ≤ k → a k - a (k - 1) ≤ -c := by
    intro k hk
    have h1 := h₁ k (le_trans hKk₀ hk)
    have h2 := hK0 k (le_trans hKK0 hk)
    rw [hc]
    linarith
  -- a grows at most linearly downwards
  have ha : ∀ m : ℕ, a (K + m) ≤ a K - (m : ℝ) * c := by
    intro m
    induction m with
    | zero => simp
    | succ p ih =>
      have hk : K ≤ K + p + 1 := by omega
      have h := hstep (K + p + 1) hk
      have he : K + p + 1 - 1 = K + p := by omega
      rw [he] at h
      have hidx : K + (p + 1) = K + p + 1 := by omega
      rw [hidx]
      push_cast
      linarith
  -- b decreases quadratically
  have hb : ∀ m : ℕ, b (K + m + 1)
      ≤ b K + ((m : ℝ) + 1) * a K - c * ((m : ℝ) * ((m : ℝ) + 1) / 2) := by
    intro m
    induction m with
    | zero =>
      have h := h₂ K hKk₀
      have h0 := ha 0
      simp only [Nat.cast_zero, add_zero] at *
      linarith
    | succ p ih =>
      have hk : k₀ ≤ K + p + 1 := by omega
      have h := h₂ (K + p + 1) hk
      have hap := ha (p + 1)
      have he : K + (p + 1) = K + p + 1 := by omega
      rw [he] at hap
      have he2 : K + (p + 1) + 1 = K + p + 1 + 1 := by omega
      rw [he2]
      push_cast at hap ⊢
      nlinarith [ih, h, hap]
  -- choose m large enough to contradict b ≥ 0
  set A : ℝ := a K with hA
  set B : ℝ := b K with hB
  obtain ⟨m, hm⟩ : ∃ m : ℕ, (|B| + |A| + 1) < c * (m : ℝ) / 2 ∧ 1 ≤ (m : ℝ) := by
    refine ⟨⌈2 * (|B| + |A| + 1) / c⌉₊ + 1, ?_, ?_⟩
    · have hle : 2 * (|B| + |A| + 1) / c ≤ (⌈2 * (|B| + |A| + 1) / c⌉₊ : ℝ) :=
        Nat.le_ceil _
      have hcn : (0 : ℝ) < c := hcpos
      push_cast
      rw [div_le_iff₀ hcn] at hle
      nlinarith [hle, hcn]
    · push_cast
      have : (0 : ℝ) ≤ (⌈2 * (|B| + |A| + 1) / c⌉₊ : ℝ) := Nat.cast_nonneg _
      linarith
  have hbm := hb m
  have hpos := h₃ (K + m + 1) (by omega)
  have habs1 : B ≤ |B| := le_abs_self B
  have habs2 : A ≤ |A| := le_abs_self A
  have hm1 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have hstep1 : ((m : ℝ) + 1) * (|B| + |A| + 1) < ((m : ℝ) + 1) * (c * (m : ℝ) / 2) :=
    mul_lt_mul_of_pos_left hm.1 (by linarith)
  have hstep2 : |B| + ((m : ℝ) + 1) * |A| + 1 ≤ ((m : ℝ) + 1) * (|B| + |A| + 1) := by
    nlinarith [mul_nonneg hm1 (abs_nonneg B), hm1, abs_nonneg A]
  have hstep3 : B + ((m : ℝ) + 1) * A ≤ |B| + ((m : ℝ) + 1) * |A| := by
    have := mul_le_mul_of_nonneg_left habs2 (by linarith : (0 : ℝ) ≤ (m : ℝ) + 1)
    linarith
  linarith [hbm, hpos, hstep1, hstep2, hstep3]
