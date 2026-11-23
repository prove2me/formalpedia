-- Prove2me | solution 1 for KernelRank.abs_exp_sub_one_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:20:19.640318+00:00
-- url     : https://prove2.me/submissions/ae4f4b4b-1b3c-4264-94ca-d2e1fa07b0fb

import Definitions.Def_KernelRankLean_Necessity
import Definitions.Def_KernelRankLean_MultiComplexRank
import Definitions.Def_KernelRankLean_MultiRealRank
import Definitions.Def_KernelRankLean_Main
import Theorems.Thm_KernelRank_expPoly_zero
import Theorems.Thm_KernelRank_fin2Vec_one
import Theorems.Thm_KernelRank_fin2Vec_zero
import Theorems.Thm_KernelRank_singleCoeff_same
attribute [local simp] KernelRank.expPoly_zero
attribute [local simp] KernelRank.fin2Vec_one
attribute [local simp] KernelRank.fin2Vec_zero
attribute [local simp] KernelRank.singleCoeff_same



set_option autoImplicit true
open Complex Polynomial Filter Topology
open KernelRank
namespace KernelRank
theorem _root_.solution (y : ℝ) :
    |Real.exp y - 1 - y| ≤ y ^ 2 * Real.exp |y| := by
  have hconv : Convex ℝ (Set.Icc (-|y|) |y|) := convex_Icc _ _
  have hy_mem : y ∈ Set.Icc (-|y|) |y| := ⟨neg_abs_le y, le_abs_self y⟩
  have h0_mem : (0 : ℝ) ∈ Set.Icc (-|y|) |y| := ⟨neg_nonpos.mpr (abs_nonneg y), abs_nonneg y⟩
  have hexp_sub_one : ∀ t ∈ Set.Icc (-|y|) |y|, ‖Real.exp t - 1‖ ≤ |y| * Real.exp |y| := by
    intro t ht
    have h1 := hconv.norm_image_sub_le_of_norm_deriv_le (f := Real.exp)
      (fun z _ => (Real.hasDerivAt_exp z).differentiableAt)
      (fun z hz => by
        rw [Real.deriv_exp, Real.norm_eq_abs, abs_of_pos (Real.exp_pos z)]
        exact Real.exp_le_exp.mpr hz.2)
      h0_mem ht
    rw [Real.exp_zero, sub_zero, Real.norm_eq_abs, Real.norm_eq_abs] at h1
    have ht_abs : |t| ≤ |y| := abs_le.mpr ht
    calc
      ‖Real.exp t - 1‖ = |Real.exp t - 1| := Real.norm_eq_abs _
      _ ≤ Real.exp |y| * |t| := h1
      _ ≤ Real.exp |y| * |y| := mul_le_mul_of_nonneg_left ht_abs (Real.exp_pos _).le
      _ = |y| * Real.exp |y| := mul_comm _ _
  have h2 := hconv.norm_image_sub_le_of_norm_deriv_le (f := fun t => Real.exp t - t)
    (fun z _ => ((Real.hasDerivAt_exp z).sub (hasDerivAt_id z)).differentiableAt)
    (fun z hz => by
      have hd : deriv (fun t => Real.exp t - t) z = Real.exp z - 1 := by simp
      rw [hd]
      exact hexp_sub_one z hz)
    h0_mem hy_mem
  rw [Real.exp_zero, sub_zero, Real.norm_eq_abs, Real.norm_eq_abs, sub_zero] at h2
  have heq1 : Real.exp y - y - 1 = Real.exp y - 1 - y := by ring
  have heq2 : |y| * Real.exp |y| * |y| = y ^ 2 * Real.exp |y| := by
    have : |y| * |y| = y ^ 2 := by rw [← sq_abs, sq]
    linear_combination Real.exp |y| * this
  rwa [heq1, heq2] at h2
end KernelRank
