-- Prove2me | solution 1 for NeuralCollapseCE.small_alpha_expansion
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-24T04:19:05.289859+00:00
-- url     : https://prove2.me/submissions/f677c637-25b2-4da1-a3a5-094fe52054eb

import Mathlib
import Definitions.Def_NeuralCollapseCE_Basic
set_option autoImplicit false
open MeasureTheory Filter Topology Asymptotics
open NeuralCollapseCE

/-- Second-order Taylor expansion of `exp` at `0`, with a cubic remainder. -/
private lemma sae_exp_taylor :
    (fun x : ℝ => Real.exp x - 1 - x - x ^ 2 / 2) =O[𝓝 0] (fun x : ℝ => x ^ 3) := by
  refine IsBigO.of_bound 1 ?_
  filter_upwards [Metric.ball_mem_nhds (0:ℝ) one_pos] with x hx
  have hx1 : |x| ≤ 1 := by
    have := Metric.mem_ball.mp hx
    rw [Real.dist_eq, sub_zero] at this
    exact this.le
  have h := Real.exp_bound hx1 (n := 3) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h
  norm_num at h
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_pow, one_mul]
  have e : Real.exp x - 1 - x - x ^ 2 / 2 = Real.exp x - (1 + x + x ^ 2 / 2) := by ring
  rw [e]
  have : |x| ^ 3 * (2 / 9) ≤ |x| ^ 3 := by
    have := pow_nonneg (abs_nonneg x) 3
    nlinarith
  linarith

/-- Second-order Taylor expansion of `log (1 + y)` at `0`, with a cubic remainder. -/
private lemma sae_log_taylor :
    (fun y : ℝ => Real.log (1 + y) - y + y ^ 2 / 2) =O[𝓝 0] (fun y : ℝ => y ^ 3) := by
  refine IsBigO.of_bound 2 ?_
  filter_upwards [Metric.ball_mem_nhds (0:ℝ) (by norm_num : (0:ℝ) < 1 / 2)] with y hy
  have hy1 : |y| < 1 / 2 := by
    have := Metric.mem_ball.mp hy
    rwa [Real.dist_eq, sub_zero] at this
  have hy1' : |-y| < 1 := by rw [abs_neg]; linarith
  have h := Real.abs_log_sub_add_sum_range_le hy1' 2
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, abs_neg] at h
  norm_num at h
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_pow]
  have e : Real.log (1 + y) - y + y ^ 2 / 2 = -y + y ^ 2 / 2 + Real.log (1 + y) := by ring
  rw [e]
  refine h.trans ?_
  have hpos : 0 < 1 - |y| := by linarith
  rw [div_le_iff₀ hpos]
  have := pow_nonneg (abs_nonneg y) 3
  nlinarith

/-- The expansion for one row: `log ∑_j exp (α b_j)` up to `O(α³)`. -/
private lemma sae_row {n : ℕ} (hn : 0 < n) (b : Fin n → ℝ) :
    (fun α : ℝ => Real.log (∑ j, Real.exp (α * b j)) -
      (Real.log n + α / n * ∑ j, b j + α ^ 2 / (2 * n) * ∑ j, b j ^ 2 -
        α ^ 2 / (2 * (n : ℝ) ^ 2) * (∑ j, b j) ^ 2))
      =O[𝓝 0] (fun α : ℝ => α ^ 3) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  set c1 : ℝ := ∑ j, b j with hc1
  set c2 : ℝ := ∑ j, b j ^ 2 with hc2
  set S : ℝ → ℝ := fun α => ∑ j, Real.exp (α * b j) with hS
  have hSpos : ∀ α, 0 < S α := fun α =>
    Finset.sum_pos (fun j _ => Real.exp_pos _) ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  set g : ℝ → ℝ := fun α => S α / n - 1 with hg
  -- per-term remainders
  have hterm : ∀ j : Fin n, (fun α : ℝ =>
      Real.exp (α * b j) - 1 - α * b j - (α * b j) ^ 2 / 2) =O[𝓝 0] (fun α : ℝ => α ^ 3) := by
    intro j
    have ht : Tendsto (fun α : ℝ => α * b j) (𝓝 0) (𝓝 0) := by
      convert (tendsto_id (x := 𝓝 (0:ℝ))).mul_const (b j) using 2 <;> simp
    have h1 := sae_exp_taylor.comp_tendsto ht
    refine h1.trans ?_
    have : (fun α : ℝ => (α * b j) ^ 3) = fun α => b j ^ 3 * α ^ 3 := by
      funext α; ring
    simp only [Function.comp_def]
    rw [this]
    exact (isBigO_refl _ _).const_mul_left _
  -- E1 = g - α c1/n - α² c2/(2n) = O(α³)
  have hE1 : (fun α : ℝ => g α - α / n * c1 - α ^ 2 / (2 * n) * c2) =O[𝓝 0]
      (fun α : ℝ => α ^ 3) := by
    have hsum := IsBigO.sum (s := Finset.univ) (fun j _ => hterm j)
    have := hsum.const_mul_left (1 / (n : ℝ))
    refine this.congr_left ?_
    intro α
    simp only [hg, hS, hc1, hc2, Finset.sum_apply]
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    rw [← Finset.mul_sum, ← Finset.sum_div]
    simp only [mul_pow, ← Finset.mul_sum]
    field_simp
  have h32 : (fun α : ℝ => α ^ 3) =O[𝓝 0] (fun α : ℝ => α ^ 2) :=
    (isLittleO_pow_pow (by norm_num : 2 < 3)).isBigO
  have h21 : (fun α : ℝ => α ^ 2) =O[𝓝 0] (fun α : ℝ => α) :=
    (isLittleO_pow_id (by norm_num : 1 < 2)).isBigO
  -- Q = g - α c1/n = O(α²)
  have hQ : (fun α : ℝ => g α - α / n * c1) =O[𝓝 0] (fun α : ℝ => α ^ 2) := by
    have h2 : (fun α : ℝ => α ^ 2 / (2 * n) * c2) =O[𝓝 0] (fun α : ℝ => α ^ 2) := by
      have : (fun α : ℝ => α ^ 2 / (2 * n) * c2) = fun α => (c2 / (2 * n)) * α ^ 2 := by
        funext α; ring
      rw [this]
      exact (isBigO_refl _ _).const_mul_left _
    refine ((hE1.trans h32).add h2).congr_left ?_
    intro α; ring
  have hlin : (fun α : ℝ => α / n * c1) =O[𝓝 0] (fun α : ℝ => α) := by
    have : (fun α : ℝ => α / n * c1) = fun α => (c1 / n) * α := by
      funext α; ring
    rw [this]
    exact (isBigO_refl _ _).const_mul_left _
  -- P = g + α c1/n = O(α), and g = O(α)
  have hgO : g =O[𝓝 0] (fun α : ℝ => α) := by
    refine ((hQ.trans h21).add hlin).congr_left ?_
    intro α; ring
  have hP : (fun α : ℝ => g α + α / n * c1) =O[𝓝 0] (fun α : ℝ => α) := hgO.add hlin
  have hg0 : Tendsto g (𝓝 0) (𝓝 0) := by
    refine hgO.trans_tendsto ?_
    exact tendsto_id
  -- log remainder
  have hL : (fun α : ℝ => Real.log (1 + g α) - g α + g α ^ 2 / 2) =O[𝓝 0]
      (fun α : ℝ => α ^ 3) :=
    (sae_log_taylor.comp_tendsto hg0).trans (hgO.pow 3)
  have hQP : (fun α : ℝ => (g α - α / n * c1) * (g α + α / n * c1)) =O[𝓝 0]
      (fun α : ℝ => α ^ 3) := by
    refine (hQ.mul hP).trans ?_
    refine (isBigO_refl _ _).congr_left ?_
    intro α; ring
  refine ((hL.add hE1).sub (hQP.const_mul_left (1 / 2))).congr_left ?_
  intro α
  have hlog : Real.log (1 + g α) = Real.log (S α) - Real.log n := by
    have : 1 + g α = S α / n := by simp only [hg]; ring
    rw [this, Real.log_div (hSpos α).ne' hn'.ne']
  rw [hlog]
  simp only [hS]
  field_simp
  ring

theorem solution {n d : ℕ} (u : Fin n → Vec d) (hu : IsUnitConfig u) :
    (fun α : ℝ =>
      ∑ i, Real.log (∑ j, Real.exp (α * inner ℝ (u i) (u j))) -
        ((n : ℝ) * Real.log n + α / n * ‖∑ i, u i‖ ^ 2 +
          α ^ 2 / (2 * n) * ∑ i, ∑ j, (inner ℝ (u i) (u j)) ^ 2 -
          α ^ 2 / (2 * (n : ℝ) ^ 2) * ∑ i, (inner ℝ (u i) (∑ j, u j)) ^ 2))
      =O[𝓝 0] (fun α : ℝ => α ^ 3) := by
  have hrows := IsBigO.sum (s := Finset.univ)
    (fun i (_ : i ∈ Finset.univ) => sae_row (Fin.pos i) (fun j => inner ℝ (u i) (u j)))
  refine hrows.congr_left ?_
  intro α
  simp only [Finset.sum_apply]
  rw [Finset.sum_sub_distrib]
  congr 1
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum, ← inner_sum]
  rw [← sum_inner, real_inner_self_eq_norm_sq]
