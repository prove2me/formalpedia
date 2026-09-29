-- Prove2me | solution 1 for MurtyKabadi.Reduction.problems1_2_equiv_problem3
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-27T22:28:05.214988+00:00
-- url     : https://prove2.me/submissions/83bfff6e-1225-46d1-b037-9e0695537091

import Mathlib
import Definitions.Def_MurtyKabadi_Reduction_QuadraticProblems

open MurtyKabadi.Reduction

private theorem Q_smul {ι : Type*} [Fintype ι] (D : Matrix ι ι ℝ) (c : ℝ) (v : ι → ℝ) :
    Q D (c • v) = c ^ 2 * Q D v := by
  simp only [Q, Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hin : ∑ j, D i j * (c * v j) = c * ∑ j, D i j * v j := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hin]
  ring

private theorem Q_zero {ι : Type*} [Fintype ι] (D : Matrix ι ι ℝ) : Q D 0 = 0 := by
  simp [Q, Matrix.mulVec, dotProduct]

theorem solution {ι : Type*} [Fintype ι] (D : Matrix ι ι ℝ) :
    (Problem1 D ↔ Problem3 D) ∧ (Problem2 D ↔ Problem3 D) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · -- Problem1 → Problem3
    intro h1
    by_contra h3
    simp only [Problem3, not_exists, not_and, not_lt] at h3
    refine h1 ?_
    have hmem : {z : ι → ℝ | Q D 0 ≤ Q D z} ∈
        nhdsWithin (0 : ι → ℝ) {x : ι → ℝ | 0 ≤ x} := by
      refine Filter.mem_of_superset self_mem_nhdsWithin ?_
      intro z hz
      simp only [Set.mem_setOf_eq]
      rw [Q_zero]
      exact h3 z hz
    exact hmem
  · -- Problem3 → Problem1
    rintro ⟨x0, hx0nn, hx0neg⟩ hmin
    obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhdsWithin_iff.mp hmin
    have hden : (0:ℝ) < 2 * (‖x0‖ + 1) := by positivity
    set c : ℝ := ε / (2 * (‖x0‖ + 1)) with hc
    have hcpos : 0 < c := by rw [hc]; positivity
    have hnorm : ‖c • x0‖ < ε := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hcpos, hc, div_mul_eq_mul_div,
        div_lt_iff₀ hden]
      have hx2 : (0:ℝ) < ‖x0‖ + 2 := by positivity
      nlinarith [mul_pos hε hx2, norm_nonneg x0]
    have hmem : c • x0 ∈ Metric.ball (0 : ι → ℝ) ε ∩ {x : ι → ℝ | 0 ≤ x} := by
      refine ⟨?_, smul_nonneg hcpos.le hx0nn⟩
      simpa [Metric.mem_ball] using hnorm
    have hge := hsub hmem
    simp only [Set.mem_setOf_eq] at hge
    rw [Q_zero, Q_smul] at hge
    have hc2pos : 0 < c ^ 2 := pow_pos hcpos 2
    nlinarith [mul_neg_of_pos_of_neg hc2pos hx0neg]
  · -- Problem2 → Problem3
    intro h2
    by_contra h3
    simp only [Problem3, not_exists, not_and, not_lt] at h3
    refine h2 ⟨0, ?_⟩
    rintro z ⟨x, hx, rfl⟩
    exact h3 x hx
  · -- Problem3 → Problem2
    rintro ⟨x0, hx0nn, hx0neg⟩ ⟨L, hL⟩
    have hqpos : 0 < -Q D x0 := by linarith
    have hratio : 0 < (|L| + 1) / (-Q D x0) := div_pos (by positivity) hqpos
    set c : ℝ := Real.sqrt ((|L| + 1) / (-Q D x0)) with hc
    have hcnn : 0 ≤ c := Real.sqrt_nonneg _
    have hc2 : c ^ 2 = (|L| + 1) / (-Q D x0) := Real.sq_sqrt hratio.le
    have hne : (-Q D x0) ≠ 0 := ne_of_gt hqpos
    have hval : Q D (c • x0) = -(|L| + 1) := by
      rw [Q_smul, hc2, div_mul_eq_mul_div, eq_comm, eq_div_iff hne]
      ring
    have hmemim : Q D (c • x0) ∈ Q D '' {x : ι → ℝ | 0 ≤ x} :=
      ⟨c • x0, smul_nonneg hcnn hx0nn, rfl⟩
    have hLle := hL hmemim
    rw [hval] at hLle
    have := neg_abs_le L
    linarith
