-- Prove2me | solution 1 for MixedORAM.PublicRead.lemma_C_1
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-13T14:50:23.180955+00:00
-- url     : https://prove2.me/submissions/6cef1f8a-decb-4622-9fd7-8cf74807659d

import Mathlib

open Filter
open scoped Topology

set_option autoImplicit false

/-- For `u ≥ 2`, `log₂ u ≤ u/2 + 2`. -/
theorem logb_two_le_half_add_two (u : ℝ) (hu : 2 ≤ u) : Real.logb 2 u ≤ u / 2 + 2 := by
  rw [Real.logb_le_iff_le_rpow (by norm_num : (1:ℝ) < 2) (by linarith : 0 < u)]
  have hsplit : (2:ℝ) ^ (u / 2 + 2) = (2:ℝ) ^ (u / 2) * 4 := by
    rw [Real.rpow_add (by norm_num : (0:ℝ) < 2)]
    norm_num
  rw [hsplit]
  have hexp : (2:ℝ) ^ (u / 2) = Real.exp (Real.log 2 * (u / 2)) :=
    Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 2) _
  rw [hexp]
  have hlog2 : (1:ℝ) / 3 < Real.log 2 / 2 := by
    have h := Real.log_two_gt_d9
    linarith
  have hu0 : (0:ℝ) ≤ u := by linarith
  have h1 : Real.exp ((1:ℝ) / 3 * u) ≤ Real.exp (Real.log 2 * (u / 2)) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have h2 : (1:ℝ) / 3 * u + 1 ≤ Real.exp ((1:ℝ) / 3 * u) := Real.add_one_le_exp _
  nlinarith

/-- If `c S ≤ x log₂(A + D/x)`, then `c' S / log₂(A + D/S) ≤ x` for a suitable `c'` depending
only on `c`. The constant is `c' = c / (4(B+2))` with `B = max(log₂(1/c), 0)`. -/
theorem solution (c : ℝ) (hc : 0 < c) :
    ∃ c' : ℝ, 0 < c' ∧ ∀ A D S x : ℝ, 2 ≤ A → 0 ≤ D → 0 < S → 0 < x →
      c * S ≤ x * Real.logb 2 (A + D / x) → c' * S / Real.logb 2 (A + D / S) ≤ x := by
  classical
  set B : ℝ := max (Real.logb 2 (1 / c)) 0 with hBdef
  have hB0 : 0 ≤ B := le_max_right _ _
  have hBbound : Real.logb 2 (1 / c) ≤ B := le_max_left _ _
  set M : ℝ := 4 * (B + 2) with hMdef
  have hMpos : 0 < M := by rw [hMdef]; positivity
  have hM4 : 4 ≤ M := by rw [hMdef]; nlinarith
  refine ⟨c / M, div_pos hc hMpos, ?_⟩
  intro A D S x hA hD hS hx hmain
  set Lx : ℝ := Real.logb 2 (A + D / x) with hLxdef
  set LS : ℝ := Real.logb 2 (A + D / S) with hLSdef
  have hmain' : c * S ≤ x * Lx := by rw [hLxdef]; exact hmain
  have hDx0 : 0 ≤ D / x := div_nonneg hD hx.le
  have hDS0 : 0 ≤ D / S := div_nonneg hD hS.le
  have hargx : 0 < A + D / x := by linarith
  have hargS : 0 < A + D / S := by linarith
  have hLx_ge1 : 1 ≤ Lx := by
    rw [hLxdef, ← Real.logb_self_eq_one (by norm_num : (1:ℝ) < 2)]
    exact Real.logb_le_logb_of_le (by norm_num) (by norm_num) (by linarith)
  have hLS_ge1 : 1 ≤ LS := by
    rw [hLSdef, ← Real.logb_self_eq_one (by norm_num : (1:ℝ) < 2)]
    exact Real.logb_le_logb_of_le (by norm_num) (by norm_num) (by linarith)
  have hLx_pos : 0 < Lx := by linarith
  have hSx_le : S / x ≤ Lx / c := by
    have h1 : c * (S / x) ≤ Lx := by
      have h2 : c * (S / x) = c * S / x := by ring
      rw [h2]
      exact (div_le_iff₀ hx).mpr (by simpa [mul_comm] using hmain')
    have h1' : S / x * c ≤ Lx := by rw [mul_comm]; exact h1
    exact (le_div_iff₀ hc).mpr h1'
  have hstep : Lx ≤ LS + max (Real.logb 2 (S / x)) 0 := by
    rcases le_or_gt S x with hSx | hSx
    · have hle : A + D / x ≤ A + D / S := by
        have hdiv : D / x ≤ D / S := by
          exact div_le_div_of_nonneg_left hD hS hSx
        linarith
      have h1 : Lx ≤ LS := by
        rw [hLxdef, hLSdef]
        exact Real.logb_le_logb_of_le (by norm_num) hargx hle
      have h2 : 0 ≤ max (Real.logb 2 (S / x)) 0 := le_max_right _ _
      linarith
    · have hSx1 : 1 ≤ S / x := (one_le_div hx).mpr hSx.le
      have hmul : A + D / x ≤ (A + D / S) * (S / x) := by
        have hDx : D / x = (D / S) * (S / x) := by
          field_simp
        have hAS : A ≤ A * (S / x) := le_mul_of_one_le_right (by linarith) hSx1
        rw [hDx]
        nlinarith
      have h1 : Lx ≤ Real.logb 2 ((A + D / S) * (S / x)) := by
        rw [hLxdef]
        exact Real.logb_le_logb_of_le (by norm_num) hargx hmul
      have h2 : Real.logb 2 ((A + D / S) * (S / x)) = LS + Real.logb 2 (S / x) := by
        rw [hLSdef, Real.logb_mul (ne_of_gt hargS) (ne_of_gt (div_pos hS hx))]
      have h3 : Real.logb 2 (S / x) ≤ max (Real.logb 2 (S / x)) 0 := le_max_left _ _
      linarith
  have hmax_bound : max (Real.logb 2 (S / x)) 0 ≤ Lx / 2 + B + 2 := by
    have hmax_le : max (Real.logb 2 (S / x)) 0 ≤ max (Real.logb 2 (Lx / c)) 0 := by
      apply max_le
      · rcases le_or_gt (S / x) 1 with h | h
        · exact le_trans (Real.logb_nonpos (by norm_num : (1:ℝ) < 2)
            (le_of_lt (div_pos hS hx)) h) (le_max_right _ _)
        · exact le_trans (Real.logb_le_logb_of_le (by norm_num) (by linarith) hSx_le)
            (le_max_left _ _)
      · exact le_max_right _ _
    have hsplit : Real.logb 2 (Lx / c) = Real.logb 2 Lx + Real.logb 2 (1 / c) := by
      have heq : Lx / c = Lx * (1 / c) := by ring
      rw [heq, Real.logb_mul (ne_of_gt hLx_pos) (by positivity)]
    have hbound : Real.logb 2 (Lx / c) ≤ Lx / 2 + B + 2 := by
      rw [hsplit]
      rcases le_or_gt Lx 2 with h | h
      · have h1 : Real.logb 2 Lx ≤ 1 := by
          have := Real.logb_le_logb_of_le (by norm_num : (1:ℝ) < 2) hLx_pos h
          rwa [Real.logb_self_eq_one (by norm_num : (1:ℝ) < 2)] at this
        linarith
      · have h1 : Real.logb 2 Lx ≤ Lx / 2 + 2 := logb_two_le_half_add_two Lx h.le
        linarith
    exact le_trans hmax_le (max_le hbound (by linarith))
  have hratio : Lx / M ≤ LS := by
    rcases lt_or_ge Lx 2 with hsmall | hbig
    · have h1 : Lx / M < 1 := by
        rw [div_lt_one hMpos]
        linarith
      linarith
    · by_contra hcon
      push Not at hcon
      have hMdiv : Lx / M ≤ Lx / 4 :=
        div_le_div_of_nonneg_left (by linarith) (by norm_num) hM4
      have hchain : Lx < 3 * Lx / 4 + (B + 2) := by
        have h1 : Lx ≤ LS + Lx / 2 + (B + 2) := by linarith
        have h2 : LS < Lx / 4 := lt_of_lt_of_le hcon hMdiv
        linarith
      have hquarter : Lx / 4 < B + 2 := by linarith
      have hLxM : Lx < M := by
        rw [hMdef]
        linarith
      have hlt : Lx / M < 1 := by
        rw [div_lt_one hMpos]
        exact hLxM
      linarith
  have hS_bound : S ≤ x * Lx / c := by
    exact (le_div_iff₀ hc).mpr (by linarith [hmain'])
  have hfinal : c / M * S ≤ x * LS := by
    have h1 : c / M * S ≤ c / M * (x * Lx / c) := by
      apply mul_le_mul_of_nonneg_left hS_bound
      positivity
    have h2 : c / M * (x * Lx / c) = x * (Lx / M) := by
      field_simp
    have h3 : x * (Lx / M) ≤ x * LS := by
      apply mul_le_mul_of_nonneg_left hratio hx.le
    linarith
  have hLS_pos : 0 < LS := by linarith
  exact (div_le_iff₀ hLS_pos).mpr hfinal
