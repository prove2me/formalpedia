-- Prove2me | solution 1 for OAI.HilbertCrouzeix.numericalClosure_geometry
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-14T18:06:37.557555+00:00
-- url     : https://prove2.me/submissions/0f376d6f-5367-4e1e-b44e-416adfff7ce1

-- Generated from openai/math@1581d4c lean/OAI/Analysis/HilbertCrouzeix/Spectrum.lean:L90-L93
-- (upload_full_project.md Phase 4): solution for the platform mission target OAI.HilbertCrouzeix.numericalClosure_geometry.
-- The statement is the platform stub (Theorems.Thm_OAI_HilbertCrouzeix_numericalClosure_geometry) verbatim; the proof is the source proof;
-- inline helpers are the source spans of the proof-only lemmas it needs.
import Mathlib
import Definitions.Def_HilbertCrouzeix
import Definitions.Def_OAI_Analysis_HilbertCrouzeix_NumericalRange
import Theorems.Thm_OAI_HilbertCrouzeix_convex_numericalRange

-- ---- inline helpers from OAI.Analysis.HilbertCrouzeix.NumericalRange ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

open Complex Set
open scoped TensorProduct Matrix.Norms.L2Operator Classical ComplexConjugate

namespace HilbertCrouzeix

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

section Elementary
omit [CompleteSpace H]

theorem norm_le_of_mem_numericalRange (A : H →L[ℂ] H) {z : ℂ}
    (hz : z ∈ numericalRange A) : ‖z‖ ≤ ‖A‖ := by
  obtain ⟨x, hx, rfl⟩ := hz
  calc
    ‖inner ℂ x (A x)‖ ≤ ‖x‖ * ‖A x‖ := norm_inner_le_norm _ _
    _ ≤ ‖x‖ * (‖A‖ * ‖x‖) := mul_le_mul_of_nonneg_left (A.le_opNorm x) (norm_nonneg x)
    _ = ‖A‖ := by rw [hx]; ring

theorem numericalRange_subset_closedBall (A : H →L[ℂ] H) :
    numericalRange A ⊆ Metric.closedBall 0 ‖A‖ := by
  intro z hz
  simpa only [Metric.mem_closedBall, dist_zero_right] using
    norm_le_of_mem_numericalRange A hz

theorem numericalClosure_subset_closedBall (A : H →L[ℂ] H) :
    numericalClosure A ⊆ Metric.closedBall 0 ‖A‖ :=
  closure_minimal (numericalRange_subset_closedBall A) Metric.isClosed_closedBall

theorem isCompact_numericalClosure (A : H →L[ℂ] H) :
    IsCompact (numericalClosure A) :=
  (isCompact_closedBall (0 : ℂ) ‖A‖).of_isClosed_subset isClosed_closure
    (numericalClosure_subset_closedBall A)

theorem convex_numericalClosure (A : H →L[ℂ] H) : Convex ℝ (numericalClosure A) :=
  (convex_numericalRange A).closure

end Elementary

end HilbertCrouzeix

end

end OAI

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

theorem solution (A : H →L[ℂ] H) :
    IsCompact (numericalClosure A) ∧ Convex ℝ (numericalClosure A) ∧
      spectrum ℂ A ⊆ numericalClosure A :=
  ⟨isCompact_numericalClosure A, convex_numericalClosure A, spectrum_subset_numericalClosure A⟩
