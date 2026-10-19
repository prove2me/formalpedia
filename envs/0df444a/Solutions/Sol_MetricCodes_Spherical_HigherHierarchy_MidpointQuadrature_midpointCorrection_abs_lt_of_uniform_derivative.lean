-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.MidpointQuadrature.midpointCorrection_abs_lt_of_uniform_derivative
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:34.162962+00:00
-- url     : https://prove2.me/submissions/29adead1-fb89-445f-bb17-b14db75dc4b7

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_MidpointQuadrature_midpoint_error_eq_derivative_difference

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option autoImplicit false
open MetricCodes
open MetricCodes.Spherical
noncomputable section
open Filter Set
open scoped Topology BigOperators
open MetricCodes.Spherical.HigherHierarchy MetricCodes.Spherical.HigherHierarchy.MidpointQuadrature
namespace MetricCodes.Spherical.HigherHierarchy.MidpointQuadrature
theorem _root_.solution
    {f g : ℝ → ℝ} (hf : ContinuousOn f (Set.Icc 0 1))
    (hderiv : ∀ x ∈ Set.Ioo 0 1, HasDerivAt f (g x) x)
    {ε δ : ℝ} (hε : 0 < ε)
    (huniform : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      ∀ y ∈ Set.Icc (0 : ℝ) 1,
        dist x y < δ → dist (g x) (g y) < ε)
    {N : ℕ} (hN : 0 < N) (hmesh : 1 / (N : ℝ) < δ) :
    |midpointCorrection f N| < ε := by
  have hN' : 0 < (N : ℝ) := by exact_mod_cast hN
  have hterm : ∀ i ∈ Finset.range N,
      |f (((i : ℝ) + 1 / 2) / N) -
        (f ((i : ℝ) / N) + f (((i : ℝ) + 1) / N)) / 2| <
          ε / (4 * N) := by
    intro i hi
    have hi' : i < N := Finset.mem_range.mp hi
    have hi_cast : (i : ℝ) < N := by exact_mod_cast hi'
    let x : ℝ := (i : ℝ) / N
    let y : ℝ := ((i : ℝ) + 1) / N
    have hx0 : 0 ≤ x := by dsimp [x]; positivity
    have hy1 : y ≤ 1 := by
      dsimp [y]
      apply (div_le_one hN').mpr
      have hi_succ : i + 1 ≤ N := Nat.succ_le_of_lt hi'
      exact_mod_cast hi_succ
    have hxy : x < y := by
      dsimp [x, y]
      exact (div_lt_div_iff_of_pos_right hN').mpr (by linarith)
    have hsub : Set.Icc x y ⊆ Set.Icc (0 : ℝ) 1 := by
      intro z hz
      exact ⟨hx0.trans hz.1, hz.2.trans hy1⟩
    obtain ⟨u, hu, v, hv, heq⟩ :=
      midpoint_error_eq_derivative_difference hxy (hf.mono hsub)
        (by
          intro z hz
          exact hderiv z ⟨lt_of_le_of_lt hx0 hz.1,
            lt_of_lt_of_le hz.2 hy1⟩)
    have huI : u ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨hx0.trans hu.1.le, ((hu.2.trans hv.1).trans hv.2).le.trans hy1⟩
    have hvI : v ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨hx0.trans ((hu.1.trans hu.2).trans hv.1).le, hv.2.le.trans hy1⟩
    have huv : u < v := hu.2.trans hv.1
    have hwidth : y - x = 1 / (N : ℝ) := by
      dsimp [x, y]
      ring
    have hdist : dist u v < δ := by
      rw [Real.dist_eq, abs_of_nonpos (by linarith : u - v ≤ 0)]
      have hdiff : v - u < y - x := by linarith [hu.1, hv.2]
      rw [hwidth] at hdiff
      linarith
    have hderivdiff : |g u - g v| < ε := by
      simpa [Real.dist_eq] using huniform u huI v hvI hdist
    have hmid : (x + y) / 2 = ((i : ℝ) + 1 / 2) / N := by
      dsimp [x, y]
      ring
    rw [← hmid, heq, abs_mul, abs_of_pos (by linarith : 0 < (y - x) / 4)]
    calc
      ((y - x) / 4) * |g u - g v| < ((y - x) / 4) * ε :=
        mul_lt_mul_of_pos_left hderivdiff (by linarith)
      _ = ε / (4 * N) := by rw [hwidth]; ring
  have hsum :
      (∑ i ∈ Finset.range N,
        |f (((i : ℝ) + 1 / 2) / N) -
          (f ((i : ℝ) / N) + f (((i : ℝ) + 1) / N)) / 2|) <
        ε / 4 := by
    have hstrict := Finset.sum_lt_sum_of_nonempty
      (Finset.nonempty_range_iff.mpr hN.ne') hterm
    calc
      (∑ i ∈ Finset.range N,
        |f (((i : ℝ) + 1 / 2) / N) -
          (f ((i : ℝ) / N) + f (((i : ℝ) + 1) / N)) / 2|) <
        ∑ _i ∈ Finset.range N, ε / (4 * N) := hstrict
      _ = ε / 4 := by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        field_simp
  calc
    |midpointCorrection f N| ≤
        ∑ i ∈ Finset.range N,
          |f (((i : ℝ) + 1 / 2) / N) -
            (f ((i : ℝ) / N) + f (((i : ℝ) + 1) / N)) / 2| := by
      exact Finset.abs_sum_le_sum_abs _ _
    _ < ε / 4 := hsum
    _ < ε := by linarith
end MetricCodes.Spherical.HigherHierarchy.MidpointQuadrature
