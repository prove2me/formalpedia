-- Prove2me | solution 1 for Mandelbrot.mandelbrot_lemniscate_antitone
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-22T12:09:23.251428+00:00
-- url     : https://prove2.me/submissions/2daad0eb-bc68-4c30-bacf-1fbb7a79a8ca

import Mathlib
import Definitions.Def_mandelbrot_sets

open Set Mandelbrot

private theorem escape_growth {z c : ℂ} (hz : 2 < ‖z‖) (hc : ‖c‖ ≤ ‖z‖) :
    ‖z‖ < ‖z ^ 2 + c‖ := by
  have hsub : ‖z‖ ^ 2 - ‖c‖ ≤ ‖z ^ 2 + c‖ := by
    have := norm_sub_norm_le (z ^ 2) (-c)
    simpa [sub_eq_add_neg, norm_neg, norm_pow] using this
  have hlt0 : ‖z‖ < ‖z‖ ^ 2 - ‖c‖ := by
    have hz1 : (1 : ℝ) < ‖z‖ - 1 ∨ (1 : ℝ) ≤ ‖z‖ - 1 := by
      have : (2 : ℝ) < ‖z‖ := hz
      left; linarith
    -- ‖z‖ < ‖z‖^2 - ‖c‖ ↔ ‖c‖ < ‖z‖(‖z‖-1)
    have : ‖c‖ < ‖z‖ * (‖z‖ - 1) := by
      have h1 : (1 : ℝ) < ‖z‖ - 1 := by linarith
      have : ‖z‖ < ‖z‖ * (‖z‖ - 1) := by
        nlinarith [norm_nonneg z]
      exact lt_of_le_of_lt hc (by nlinarith)
    nlinarith
  exact lt_of_lt_of_le hlt0 hsub

private theorem orbit_ge_abs_c {c : ℂ} (hc : 2 < ‖c‖) :
    ∀ m : ℕ, ‖c‖ ≤ ‖(fun z : ℂ ↦ z ^ 2 + c)^[m + 1] 0‖ ∧
      2 < ‖(fun z : ℂ ↦ z ^ 2 + c)^[m + 1] 0‖ := by
  intro m
  induction m with
  | zero =>
    constructor <;> simp [hc]
  | succ m ih =>
    obtain ⟨hle, hlt⟩ := ih
    have hnext := escape_growth hlt hle
    -- ‖p^[m+2] 0‖ = ‖p^[m+1] 0 ^ 2 + c‖
    have heq : (fun z : ℂ ↦ z ^ 2 + c)^[m + 1 + 1] 0 =
        (fun z : ℂ ↦ z ^ 2 + c)^[m + 1] 0 ^ 2 + c := by
      rw [Function.iterate_succ_apply']
    refine ⟨?_, ?_⟩
    · simpa [heq] using (le_trans hle hnext.le)
    · simpa [heq] using (lt_trans hlt hnext)

private theorem abs_c_le_of_later_bound {c : ℂ} {n : ℕ} (hn : 1 ≤ n)
    (hb : ‖(fun z : ℂ ↦ z ^ 2 + c)^[n] 0‖ ≤ 2) : ‖c‖ ≤ 2 := by
  by_contra h
  push_neg at h
  obtain ⟨_, hlt⟩ := orbit_ge_abs_c h (n - 1)
  have : n - 1 + 1 = n := Nat.sub_add_cancel hn
  simp only [this] at hlt
  exact (not_lt_of_ge hb) hlt

theorem solution (k : ℕ) :
    {c : ℂ | ‖(fun z ↦ z ^ 2 + c)^[k + 1] 0‖ ≤ 2} ⊆
      {c : ℂ | ‖(fun z ↦ z ^ 2 + c)^[k] 0‖ ≤ 2} := by
  intro c hc
  simp only [mem_setOf_eq] at hc ⊢
  by_cases hk : k = 0
  · subst hk; simp
  · have hc2 : ‖c‖ ≤ 2 := abs_c_le_of_later_bound (by omega : 1 ≤ k + 1) hc
    by_contra h
    push_neg at h
    have hle : ‖c‖ ≤ ‖(fun z : ℂ ↦ z ^ 2 + c)^[k] 0‖ := le_trans hc2 (le_of_lt h)
    have hgrow := escape_growth h hle
    rw [Function.iterate_succ_apply'] at hc
    exact (not_lt_of_ge hc) (lt_trans h hgrow)
