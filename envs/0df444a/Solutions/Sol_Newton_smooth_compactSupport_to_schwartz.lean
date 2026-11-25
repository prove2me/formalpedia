-- Prove2me | solution 1 for Newton.smooth_compactSupport_to_schwartz
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:27:47.285442+00:00
-- url     : https://prove2.me/submissions/48f215dd-2f52-43be-bb6e-4f4b863408d7

import Mathlib.Analysis.Distribution.SchwartzSpace
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.Topology.Algebra.Support
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.SmoothApprox
import Definitions.Def_Newton_MeasureTheory_Function_LpSpace_ContinuousDense

set_option autoImplicit false
open MeasureTheory NNReal SchwartzMap
open scoped ENNReal ContDiff Topology
open Newton
variable {n : ℕ}
namespace Newton
theorem _root_.solution
    (g : (Fin n → ℝ) → ℂ)
    (hg_smooth : ContDiff ℝ (∞ : WithTop ℕ∞) g)
    (hg_support : HasCompactSupport g) :
    ∃ φ : 𝓢((Fin n → ℝ), ℂ), (φ : (Fin n → ℝ) → ℂ) = g := by
  have h_decay : ∀ k m : ℕ, ∃ C : ℝ,
      ∀ x : (Fin n → ℝ), ‖x‖ ^ k * ‖iteratedFDeriv ℝ m g x‖ ≤ C := by
    intro k m
    set K := tsupport g with hK_def
    have hK_compact : IsCompact K := hg_support
    have h_iter_subset : tsupport (iteratedFDeriv ℝ m g) ⊆ K := by
      simpa [hK_def] using
        (tsupport_iteratedFDeriv_subset (𝕜 := ℝ) (f := g) (n := m))
    set h : (Fin n → ℝ) → ℝ := fun x => ‖x‖ ^ k * ‖iteratedFDeriv ℝ m g x‖
    have h_nonneg : ∀ x, 0 ≤ h x := fun x =>
      mul_nonneg (pow_nonneg (norm_nonneg _) _) (norm_nonneg _)
    by_cases h_support_empty : tsupport (iteratedFDeriv ℝ m g) = (∅ : Set (Fin n → ℝ))
    · refine ⟨0, ?_⟩
      intro x
      have hx_not : x ∉ tsupport (iteratedFDeriv ℝ m g) := by
        simp [h_support_empty]
      have hx_zero : iteratedFDeriv ℝ m g x = 0 :=
        image_eq_zero_of_notMem_tsupport hx_not
      simp [hx_zero]
    · have h_support_nonempty : (tsupport (iteratedFDeriv ℝ m g)).Nonempty :=
        Set.nonempty_iff_ne_empty.mpr h_support_empty
      obtain ⟨x₀, hx₀_support⟩ := h_support_nonempty
      have hx₀K : x₀ ∈ K := h_iter_subset hx₀_support
      have h_pow_cont : Continuous fun x : (Fin n → ℝ) => ‖x‖ ^ k :=
        (continuous_norm : Continuous fun x => ‖x‖).pow _
      have h_iter_cont : Continuous fun x : (Fin n → ℝ) => iteratedFDeriv ℝ m g x :=
        hg_smooth.continuous_iteratedFDeriv (hm := by
          exact_mod_cast (le_top : (m : ℕ∞) ≤ (⊤ : ℕ∞)))
      have h_cont : Continuous h :=
        h_pow_cont.mul (h_iter_cont.norm)
      have h_image_compact : IsCompact (h '' K) := hK_compact.image h_cont
      have h_image_nonempty : (h '' K).Nonempty := ⟨h x₀, ⟨x₀, hx₀K, rfl⟩⟩
      obtain ⟨C, hC_isGreatest⟩ :=
        h_image_compact.exists_isGreatest h_image_nonempty
      obtain ⟨⟨xC, hxC_K, rfl⟩, hC_max⟩ := hC_isGreatest
      refine ⟨h xC, ?_⟩
      intro x
      by_cases hxK : x ∈ K
      · have hx_mem : h x ∈ h '' K := ⟨x, hxK, rfl⟩
        exact hC_max hx_mem
      · have hx_not : x ∉ tsupport (iteratedFDeriv ℝ m g) := fun hx => hxK (h_iter_subset hx)
        have hx_zero : iteratedFDeriv ℝ m g x = 0 :=
          image_eq_zero_of_notMem_tsupport hx_not
        have hx_val : h x = 0 := by simp [h, hx_zero]
        have hxC_nonneg : 0 ≤ h xC := h_nonneg xC
        have hx_le : h x ≤ h xC := by simpa [hx_val] using hxC_nonneg
        exact hx_le
  refine ⟨⟨g, hg_smooth, h_decay⟩, rfl⟩
end Newton
