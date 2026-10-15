-- Prove2me | solution 1 for OAI.HilbertCrouzeix.rational_denominator_isUnit
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-14T18:11:44.422399+00:00
-- url     : https://prove2.me/submissions/819badea-40dc-4b53-90bb-978ac4ea7c2d

-- Generated from openai/math@1581d4c lean/OAI/Analysis/HilbertCrouzeix/Calculus.lean:L51-L57
-- (upload_full_project.md Phase 4): solution for the platform mission target OAI.HilbertCrouzeix.rational_denominator_isUnit.
-- The statement is the platform stub (Theorems.Thm_OAI_HilbertCrouzeix_rational_denominator_isUnit) verbatim; the proof is the source proof;
-- inline helpers are the source spans of the proof-only lemmas it needs.
import Mathlib
import Definitions.Def_HilbertCrouzeix
import Definitions.Def_OAI_Analysis_HilbertCrouzeix_NumericalRange

-- ---- inline helpers from OAI.Analysis.HilbertCrouzeix.Spectrum ----
namespace OAI

noncomputable section

open Complex Set
open scoped TensorProduct Matrix.Norms.L2Operator Classical ComplexConjugate

namespace HilbertCrouzeix

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

section Elementary
omit [CompleteSpace H]

theorem lowerBound_of_unit_inner (T : H →L[ℂ] H) {δ : ℝ}
    (h : ∀ x : H, ‖x‖ = 1 → δ ≤ ‖inner ℂ x (T x)‖) (x : H) :
    δ * ‖x‖ ≤ ‖T x‖ := by
  by_cases hx : x = 0
  · simp [hx]
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  let y : H := (‖x‖ : ℂ)⁻¹ • x
  have hy : ‖y‖ = 1 := norm_smul_inv_norm hx
  have hl : δ ≤ ‖T y‖ := calc
    δ ≤ ‖inner ℂ y (T y)‖ := h y hy
    _ ≤ ‖y‖ * ‖T y‖ := norm_inner_le_norm _ _
    _ = ‖T y‖ := by rw [hy, one_mul]
  calc
    δ * ‖x‖ ≤ ‖T y‖ * ‖x‖ := mul_le_mul_of_nonneg_right hl (norm_nonneg x)
    _ = ‖T x‖ := by
      simp only [y, map_smul, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
        abs_norm]
      field_simp

theorem antilipschitz_of_lowerBound (T : H →L[ℂ] H) {δ : ℝ} (hδ : 0 < δ)
    (h : ∀ x : H, δ * ‖x‖ ≤ ‖T x‖) :
    AntilipschitzWith ⟨δ⁻¹, inv_nonneg.mpr hδ.le⟩ T := by
  apply AntilipschitzWith.of_le_mul_dist
  intro x y
  simp only [dist_eq_norm]
  change ‖x - y‖ ≤ δ⁻¹ * ‖T x - T y‖
  rw [← map_sub, inv_mul_eq_div]
  exact (le_div_iff₀ hδ).mpr (by simpa only [mul_comm] using h (x - y))

end Elementary

theorem isUnit_of_unit_inner (T : H →L[ℂ] H) {δ : ℝ} (hδ : 0 < δ)
    (h : ∀ x : H, ‖x‖ = 1 → δ ≤ ‖inner ℂ x (T x)‖) : IsUnit T := by
  have hl := antilipschitz_of_lowerBound T hδ (lowerBound_of_unit_inner T h)
  have hadj : ∀ x : H, ‖x‖ = 1 → δ ≤ ‖inner ℂ x (T.adjoint x)‖ := by
    intro x hx
    rw [ContinuousLinearMap.adjoint_inner_right, norm_inner_symm]
    exact h x hx
  have hla := antilipschitz_of_lowerBound T.adjoint hδ
    (lowerBound_of_unit_inner T.adjoint hadj)
  have hc : IsClosed (T.toLinearMap.range : Set H) := hl.isClosed_range T.uniformContinuous
  have hbot : T.toLinearMap.rangeᗮ = ⊥ := by
    rw [T.orthogonal_range]
    exact LinearMap.ker_eq_bot.mpr hla.injective
  have htop : T.toLinearMap.range = ⊤ := by
    rw [← hc.submodule_topologicalClosure_eq]
    exact Submodule.topologicalClosure_eq_top_iff.mpr hbot
  exact ContinuousLinearMap.isUnit_iff_bijective.mpr
    ⟨hl.injective, LinearMap.range_eq_top.mp htop⟩

theorem spectrum_subset_numericalClosure (A : H →L[ℂ] H) :
    spectrum ℂ A ⊆ numericalClosure A := by
  intro z hz
  by_contra hnot
  obtain ⟨δ, hδ, hb⟩ := Metric.isOpen_iff.mp
    (isClosed_closure.isOpen_compl) z hnot
  have hdist : ∀ w ∈ numericalRange A, δ ≤ ‖z - w‖ := by
    intro w hw
    by_contra! hlt
    have hw' : w ∈ Metric.ball z δ := by
      simpa only [Metric.mem_ball, dist_eq_norm, norm_sub_rev] using hlt
    exact hb hw' (subset_closure hw)
  have hu : IsUnit ((algebraMap ℂ (H →L[ℂ] H)) z - A) := by
    apply isUnit_of_unit_inner _ hδ
    intro x hx
    simpa only [sub_apply, ContinuousLinearMap.algebraMap_apply,
      inner_sub_right, inner_smul_right, inner_self_eq_norm_sq_to_K, hx,
      RCLike.ofReal_one, one_pow, mul_one] using
      hdist (inner ℂ x (A x)) ⟨x, hx, rfl⟩
  exact spectrum.mem_iff.mp hz hu

end HilbertCrouzeix

end

end OAI

-- ---- hoisted mission target ----
open OAI OAI.HilbertCrouzeix
open Complex Set
open scoped TensorProduct Matrix.Norms.L2Operator Classical ComplexConjugate
universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable [CompleteSpace H]

theorem solution [Nontrivial H] (A : H →L[ℂ] H)
    {m : ℕ} (R : RationalMatrix m) (hR : numericalClosure A ⊆ poleFreeSet R)
    (i j : Fin m) : IsUnit (Polynomial.aeval A (R i j).denom) := by
  apply (spectrum.zero_notMem_iff ℂ).mp
  rw [spectrum.map_polynomial_aeval]
  rintro ⟨z, hz, hz0⟩
  exact hR (spectrum_subset_numericalClosure A hz) i j hz0
