-- Prove2me | solution 1 for GlobalTheory.plane_lattice_reduction_step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:29:12.846295+00:00
-- url     : https://prove2.me/submissions/50dd3d5a-04c8-486a-8e73-06ba62da1f72

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_PlaneLatticeShortBasisOfBoundPowTwo

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (e₁ e₂ : ℂ)
    (h : 2 * |((starRingEnd ℂ) e₁ * e₂).im| < ‖e₁‖ ^ 2) :
    ∃ f₁ f₂ : ℂ, Submodule.span ℤ {f₁, f₂} = Submodule.span ℤ {e₁, e₂} ∧
      |((starRingEnd ℂ) f₁ * f₂).im| = |((starRingEnd ℂ) e₁ * e₂).im| ∧
      2 * ‖f₁‖ ^ 2 ≤ ‖e₁‖ ^ 2 := by
  have hN : 0 < ‖e₁‖ ^ 2 := lt_of_le_of_lt (by positivity) h
  set k : ℤ := round (((starRingEnd ℂ) e₁ * e₂).re / ‖e₁‖ ^ 2) with hk
  refine ⟨e₂ - k • e₁, e₁, ?_, ?_, ?_⟩
  · apply le_antisymm
    · rw [Submodule.span_le]
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact Submodule.sub_mem _ (Submodule.subset_span (by simp))
          (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      · exact Submodule.subset_span (by simp)
    · rw [Submodule.span_le]
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact Submodule.subset_span (by simp)
      · have : x = (x - k • e₁) + k • e₁ := by ring
        rw [SetLike.mem_coe]
        nth_rewrite 2 [this]
        exact Submodule.add_mem _ (Submodule.subset_span (by simp))
          (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
  · have : ((starRingEnd ℂ) (e₂ - k • e₁) * e₁).im = -((starRingEnd ℂ) e₁ * e₂).im := by
      simp
      ring
    rw [this, abs_neg]
  · have hr := abs_sub_round (((starRingEnd ℂ) e₁ * e₂).re / ‖e₁‖ ^ 2)
    rw [← hk] at hr
    have key : ‖e₁‖ ^ 2 * ‖e₂ - k • e₁‖ ^ 2 =
        (((starRingEnd ℂ) e₁ * e₂).re - k * ‖e₁‖ ^ 2) ^ 2 +
          ((starRingEnd ℂ) e₁ * e₂).im ^ 2 := by
      simp only [Complex.sq_norm, Complex.normSq_apply]
      simp
      ring
    generalize ((starRingEnd ℂ) e₁ * e₂).re = R at *
    generalize ((starRingEnd ℂ) e₁ * e₂).im = J at *
    generalize ‖e₁‖ ^ 2 = N at *
    generalize ‖e₂ - k • e₁‖ ^ 2 = M at *
    have h1 : (R - k * N) ^ 2 ≤ N ^ 2 / 4 := by
      have e : R - k * N = (R / N - k) * N := by field_simp
      have h2 : (R / N - k) ^ 2 ≤ 1 / 4 := by
        rw [← sq_abs]
        nlinarith [abs_nonneg (R / N - k)]
      rw [e, mul_pow]
      nlinarith [sq_nonneg N]
    have h3 : J ^ 2 ≤ N ^ 2 / 4 := by
      rw [← sq_abs J]
      nlinarith [abs_nonneg J]
    have h4 : N * (2 * M) ≤ N * N := by nlinarith
    exact le_of_mul_le_mul_left h4 hN
end GlobalTheory
