-- Prove2me | solution 1 for Kyprianou.Ch04.uniformBoundedMultiplierV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T21:26:22.806036+00:00
-- url     : https://prove2.me/submissions/73a14dcf-361c-4045-a928-ab4b3b1259f3

import Mathlib.Topology.MetricSpace.Pseudo.Basic
open Filter Set
open scoped Topology
set_option autoImplicit false

/-- Uniform convergence on a set is preserved by multiplication by a
fixed uniformly bounded scalar field on that set. -/
theorem solution {I : Type} [Preorder I] [Nonempty I] (F : I → ℝ → ℝ)
    (g h : ℝ → ℝ) (s : Set ℝ) (M : ℝ)
    (hM : 0 ≤ M) (hb : ∀ u ∈ s, |h u| ≤ M)
    (hF : TendstoUniformlyOn F g atTop s) :
    TendstoUniformlyOn (fun i u => F i u * h u)
      (fun u => g u * h u) atTop s := by
  rw [Metric.tendstoUniformlyOn_iff] at hF ⊢
  intro ε hε
  have hDen : 0 < M + 1 := by linarith
  have hδ : 0 < ε / (M + 1) := div_pos hε hDen
  filter_upwards [hF (ε / (M + 1)) hδ] with i hi u hu
  have hsmall : |F i u - g u| < ε / (M + 1) := by
    simpa only [Real.dist_eq, abs_sub_comm] using hi u hu
  rw [dist_comm, Real.dist_eq, abs_sub_comm]
  calc
    |g u * h u - F i u * h u| =
        |F i u - g u| * |h u| := by rw [←sub_mul, abs_mul, abs_sub_comm]
    _ ≤ |F i u - g u| * M :=
      mul_le_mul_of_nonneg_left (hb u hu) (abs_nonneg _)
    _ ≤ (ε / (M + 1)) * M :=
      mul_le_mul_of_nonneg_right hsmall.le hM
    _ < ε := by
      have hstep : ε / (M + 1) * M <
          ε / (M + 1) * (M + 1) :=
        mul_lt_mul_of_pos_left (by linarith) hδ
      rw [div_mul_cancel₀ ε (ne_of_gt hDen)] at hstep
      exact hstep
