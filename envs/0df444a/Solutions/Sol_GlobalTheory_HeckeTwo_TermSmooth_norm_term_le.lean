-- Prove2me | solution 1 for GlobalTheory.HeckeTwo.TermSmooth.norm_term_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:05:41.858826+00:00
-- url     : https://prove2.me/submissions/fcda2bbd-822c-4c12-b6c1-d89a6fc692f3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContDiffOnHeckeEisensteinFourierTerm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo
noncomputable section
open GlobalTheory GlobalTheory.HeckeTwo GlobalTheory.HeckeTwo.TermSmooth
namespace GlobalTheory.HeckeTwo.TermSmooth
theorem _root_.solution (σ : ℂ) (hσ : σ ∈ halfPlane) (ν : ℝ) (a b m : ℕ) (hab : 2 ≤ a + 2 * b) {y₀ : ℝ}
    (hy₀ : y₀ ≠ 0) : ∃ bd : ℝ → ℝ, MeasureTheory.Integrable bd ∧
      ∀ t, ∀ y ∈ Metric.ball y₀ (|y₀| / 2), ‖term σ ν a b m y t‖ ≤ bd t := by
  have hσ' : -1 / 2 < σ.re := hσ
  set c := |y₀| / 2 with hc
  have hc0 : 0 < c := by positivity
  set e : ℝ := (a : ℝ) / 2 + b + σ.re with he
  have hab' : (2 : ℝ) ≤ a + 2 * b := by exact_mod_cast hab
  have he1 : 1 / 2 < e := by rw [he]; linarith
  set κ := min 1 (c ^ 2) with hκ
  have hκ0 : 0 < κ := lt_min one_pos (by positivity)
  refine ⟨fun t => (3 * c) ^ m * κ ^ (-e) * (1 + ‖t‖ ^ 2) ^ (-(2 * e) / 2), ?_, ?_⟩
  · exact (integrable_rpow_neg_one_add_norm_sq (by simp; linarith)).const_mul _
  intro t y hy
  rw [Metric.mem_ball, Real.dist_eq] at hy
  have hyl : c ≤ |y| := by
    have := abs_sub_abs_le_abs_sub y₀ y
    rw [abs_sub_comm] at this; rw [hc]; linarith
  have hyu : |y| ≤ 3 * c := by
    have := abs_sub_abs_le_abs_sub y y₀
    rw [hc]; linarith
  have hy0 : y ≠ 0 := fun h => by rw [h, abs_zero] at hyl; linarith
  have hQ : 0 < t ^ 2 + y ^ 2 := by positivity
  have hnu : ‖(t : ℂ) + (y : ℂ) * I‖ = Real.sqrt (t ^ 2 + y ^ 2) := by
    rw [← Complex.normSq_add_mul_I, Complex.norm_def]
  have hnorm : ‖term σ ν a b m y t‖ = (t ^ 2 + y ^ 2) ^ (-e) * |y| ^ m := by
    unfold term
    rw [norm_mul, norm_mul, norm_mul, norm_pow, norm_inv, hnu, Complex.norm_cpow_eq_rpow_re_of_pos hQ,
      norm_pow, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp]
    have hre : (-(2 * (Real.pi : ℂ) * I * (ν : ℂ) * (t : ℂ))).re = 0 := by simp
    rw [hre, Real.exp_zero, mul_one, he, Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_neg_one,
      ← Real.rpow_mul hQ.le, ← Real.rpow_mul hQ.le, ← Real.rpow_add hQ]
    congr 2
    simp
    ring
  rw [hnorm]
  have hQk : κ * (1 + ‖t‖ ^ 2) ≤ t ^ 2 + y ^ 2 := by
    rw [Real.norm_eq_abs, sq_abs]
    have h1 : κ ≤ 1 := min_le_left _ _
    have h2 : κ ≤ c ^ 2 := min_le_right _ _
    have h3 : c ^ 2 ≤ y ^ 2 := by rw [← sq_abs y]; exact pow_le_pow_left₀ hc0.le hyl 2
    nlinarith [sq_nonneg t]
  have hA : (t ^ 2 + y ^ 2) ^ (-e) ≤ κ ^ (-e) * (1 + ‖t‖ ^ 2) ^ (-(2 * e) / 2) := by
    rw [show -(2 * e) / 2 = -e by ring, ← Real.mul_rpow hκ0.le (by positivity)]
    exact Real.rpow_le_rpow_of_nonpos (by positivity) hQk (by linarith)
  have hB : |y| ^ m ≤ (3 * c) ^ m := pow_le_pow_left₀ (abs_nonneg y) hyu m
  calc (t ^ 2 + y ^ 2) ^ (-e) * |y| ^ m ≤ (κ ^ (-e) * (1 + ‖t‖ ^ 2) ^ (-(2 * e) / 2)) * (3 * c) ^ m :=
        mul_le_mul hA hB (by positivity) (by positivity)
    _ = _ := by ring
end GlobalTheory.HeckeTwo.TermSmooth
