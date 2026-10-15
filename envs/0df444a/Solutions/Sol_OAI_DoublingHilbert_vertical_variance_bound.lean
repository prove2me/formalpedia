-- Prove2me | solution 1 for OAI.DoublingHilbert.vertical_variance_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-14T23:25:08.537137+00:00
-- url     : https://prove2.me/submissions/d4e7c7b9-6275-4efe-b28e-79e401ad9c0a

-- Generated from openai/math@1581d4c lean/OAI/Geometry/DoublingHilbert/Extremal.lean:L147-L170
-- (upload_full_project.md Phase 4): solution for node OAI.DoublingHilbert.vertical_variance_bound. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib
import Definitions.Def_DoublingHilbert
import Definitions.Def_OAI_Geometry_DoublingHilbert_Construction
import Definitions.Def_OAI_Geometry_DoublingHilbert_Derivatives
import Definitions.Def_OAI_Geometry_DoublingHilbert_Integration
import Definitions.Def_OAI_Geometry_DoublingHilbert_Rectangles
import Definitions.Def_OAI_Geometry_DoublingHilbert_Grids
import Definitions.Def_OAI_Geometry_DoublingHilbert_SelectedSheets
import Theorems.Thm_OAI_DoublingHilbert_integral_variance_identity

-- ---- from OAI.Geometry.DoublingHilbert.Extremal ----
namespace OAI

/-! Compact lexicographic extrema and quantitative second-moment estimates. -/

open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace DoublingHilbert
open MeasureTheory
open scoped BigOperators

section Moments

variable {X E : Type*} [MeasurableSpace X] {μ : Measure X}
  [IsProbabilityMeasure μ] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]

/-- Small moment error and an upper second moment force small mean-square variation. -/
theorem variance_le_of_moments {G : X → E} (hG : Integrable G μ)
    (hG2 : Integrable (fun x => ‖G x‖ ^ 2) μ) (a : E) {M : ℝ}
    (hM : (∫ x, ‖G x‖ ^ 2 ∂μ) ≤ M) :
    (∫ x, ‖G x - a‖ ^ 2 ∂μ) ≤ M - ‖a‖ ^ 2 +
      2 * ‖a‖ * ‖(∫ x, G x ∂μ) - a‖ := by
  rw [integral_variance_identity hG hG2 a]
  have h := real_inner_le_norm (-a) ((∫ x, G x ∂μ) - a)
  simp only [inner_neg_left, norm_neg] at h
  nlinarith

/-- Discarding the nonnegative variance bounds the second-moment deficit. -/
theorem mean_deficit_le {G : X → E} (hG : Integrable G μ)
    (hG2 : Integrable (fun x => ‖G x‖ ^ 2) μ) (a : E) (A : ℝ) :
    A - (∫ x, ‖G x‖ ^ 2 ∂μ) ≤ A - ‖a‖ ^ 2 +
      2 * ‖a‖ * ‖(∫ x, G x ∂μ) - a‖ := by
  have hnonneg : 0 ≤ (∫ x, ‖G x - a‖ ^ 2 ∂μ) := integral_nonneg fun _ => sq_nonneg _
  rw [integral_variance_identity hG hG2 a] at hnonneg
  have h := real_inner_le_norm (-a) ((∫ x, G x ∂μ) - a)
  simp only [inner_neg_left, norm_neg] at h
  nlinarith

/-- Integrated affine barrier; unlike a limsup statement, this keeps all quantitative data. -/
theorem integral_second_le_barrier {K : Set (ℝ × ℝ)} {s t : X → ℝ}
    (hs : Integrable s μ) (ht : Integrable t μ)
    (hvalues : ∀ᵐ x ∂μ, (s x, t x) ∈ K) {A B ε C : ℝ}
    (hbarrier : ∀ p ∈ K, p.2 ≤ B + ε + C * (A - p.1)) :
    (∫ x, t x ∂μ) ≤ B + ε + C * (A - ∫ x, s x ∂μ) := by
  have hi : Integrable (fun x => B + ε + C * (A - s x)) μ :=
    (integrable_const _).add (((integrable_const _).sub hs).const_mul _)
  have hle := integral_mono_ae ht hi (hvalues.mono fun x hx => hbarrier _ hx)
  simpa only [integral_add (f := fun _ => B + ε) (g := fun x => C * (A - s x))
      (integrable_const _) (((integrable_const _).sub hs).const_mul _),
    integral_const_mul, integral_sub (integrable_const _) hs, integral_const,
    probReal_univ, smul_eq_mul, one_mul] using hle

/-- The hard lexicographic energy step, before substituting the geometric moment bounds. -/
theorem vertical_variance_bound
    {G H : X → E} (hG : Integrable G μ) (hG2 : Integrable (fun x => ‖G x‖ ^ 2) μ)
    (hH : Integrable H μ) (hH2 : Integrable (fun x => ‖H x‖ ^ 2) μ)
    {K : Set (ℝ × ℝ)} (hvalues : ∀ᵐ x ∂μ, (‖G x‖ ^ 2, ‖H x‖ ^ 2) ∈ K)
    {A B ε C D : ℝ} (hC : 0 ≤ C)
    (hbarrier : ∀ p ∈ K, p.2 ≤ B + ε + C * (A - p.1))
    (u v : E) (hu : ‖u‖ ≤ D) (hv : ‖v‖ ≤ D) :
    (∫ x, ‖H x - v‖ ^ 2 ∂μ) ≤ B - ‖v‖ ^ 2 + ε +
      C * (A - ‖u‖ ^ 2 + 2 * D * ‖(∫ x, G x ∂μ) - u‖) +
      2 * D * ‖(∫ x, H x ∂μ) - v‖ := by
  have hb := integral_second_le_barrier hG2 hH2 hvalues hbarrier
  have hvb := variance_le_of_moments hH hH2 v hb
  have hdef := mean_deficit_le hG hG2 u A
  have hdu : 2 * ‖u‖ * ‖(∫ x, G x ∂μ) - u‖ ≤
      2 * D * ‖(∫ x, G x ∂μ) - u‖ := by
    gcongr
  have hdv : 2 * ‖v‖ * ‖(∫ x, H x ∂μ) - v‖ ≤
      2 * D * ‖(∫ x, H x ∂μ) - v‖ := by
    gcongr
  have hdef' : A - (∫ x, ‖G x‖ ^ 2 ∂μ) ≤
      A - ‖u‖ ^ 2 + 2 * D * ‖(∫ x, G x ∂μ) - u‖ := by linarith
  have hdef'' := mul_le_mul_of_nonneg_left hdef' hC
  linarith

end Moments

end DoublingHilbert

end OAI

-- ---- platform node ----
open OAI OAI.DoublingHilbert
open MeasureTheory Set Filter
open scoped BigOperators Topology
open MeasureTheory
open scoped BigOperators
variable {X E : Type*} [MeasurableSpace X] {μ : Measure X}
  [IsProbabilityMeasure μ] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]

theorem solution
    {G H : X → E} (hG : Integrable G μ) (hG2 : Integrable (fun x => ‖G x‖ ^ 2) μ)
    (hH : Integrable H μ) (hH2 : Integrable (fun x => ‖H x‖ ^ 2) μ)
    {K : Set (ℝ × ℝ)} (hvalues : ∀ᵐ x ∂μ, (‖G x‖ ^ 2, ‖H x‖ ^ 2) ∈ K)
    {A B ε C D : ℝ} (hC : 0 ≤ C)
    (hbarrier : ∀ p ∈ K, p.2 ≤ B + ε + C * (A - p.1))
    (u v : E) (hu : ‖u‖ ≤ D) (hv : ‖v‖ ≤ D) :
    (∫ x, ‖H x - v‖ ^ 2 ∂μ) ≤ B - ‖v‖ ^ 2 + ε +
      C * (A - ‖u‖ ^ 2 + 2 * D * ‖(∫ x, G x ∂μ) - u‖) +
      2 * D * ‖(∫ x, H x ∂μ) - v‖ := by
  first
    | exact OAI.DoublingHilbert.vertical_variance_bound hG hG2 hH hH2 hvalues hC hbarrier u v hu hv
    | exact OAI.DoublingHilbert.vertical_variance_bound
    | (apply OAI.DoublingHilbert.vertical_variance_bound <;> assumption)
    | (intros; apply OAI.DoublingHilbert.vertical_variance_bound <;> assumption)
