-- Prove2me | solution 1 for Irrational.exists_int_linear_forms_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @Lucas
-- created : 2026-09-10T21:24:03.304994+00:00
-- url     : https://prove2.me/submissions/859f21ff-6700-429b-9d19-adb617c3471b

import Mathlib

open Filter Topology

theorem solution {x : ℝ} (hx : Irrational x) :
    ∃ p q : ℕ → ℤ, (∀ n, 0 < q n) ∧
      (∀ n, (q n : ℝ) * x - (p n : ℝ) ≠ 0) ∧
      Filter.Tendsto (fun n => (q n : ℝ) * x - (p n : ℝ)) Filter.atTop (nhds 0) := by
  have key : ∀ n : ℕ, ∃ jk : ℤ × ℤ, 0 < jk.2 ∧
      |(jk.2 : ℝ) * x - (jk.1 : ℝ)| ≤ 1 / ((n : ℝ) + 1) := by
    intro n
    obtain ⟨j, k, hk₀, -, h⟩ := Real.exists_int_int_abs_mul_sub_le x (n := n + 1) (by omega)
    refine ⟨(j, k), hk₀, h.trans ?_⟩
    have h1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have h2 : ((n : ℝ) + 1) ≤ ((n : ℕ) + 1 : ℕ) + 1 := by push_cast; linarith
    exact one_div_le_one_div_of_le h1 h2
  choose F hFpos hFle using key
  refine ⟨fun n => (F n).1, fun n => (F n).2, hFpos, ?_, ?_⟩
  · intro n h0
    have hk : ((F n).2 : ℝ) ≠ 0 := by exact_mod_cast (hFpos n).ne'
    apply hx
    refine ⟨((F n).1 : ℚ) / ((F n).2 : ℚ), ?_⟩
    push_cast
    field_simp
    linarith [h0]
  · exact squeeze_zero_norm (fun n => hFle n) tendsto_one_div_add_atTop_nhds_zero_nat
