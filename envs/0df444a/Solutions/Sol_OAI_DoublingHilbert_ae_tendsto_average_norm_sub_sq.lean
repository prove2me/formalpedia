-- Prove2me | solution 1 for OAI.DoublingHilbert.ae_tendsto_average_norm_sub_sq
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-14T22:55:58.924686+00:00
-- url     : https://prove2.me/submissions/a536374f-02c8-4797-b040-d8bcaab95f9d

-- Generated from openai/math@1581d4c lean/OAI/Geometry/DoublingHilbert/Derivatives.lean:L31-L65
-- (upload_full_project.md Phase 4): solution for node OAI.DoublingHilbert.ae_tendsto_average_norm_sub_sq. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib
import Definitions.Def_DoublingHilbert
import Definitions.Def_OAI_Geometry_DoublingHilbert_Construction
import Definitions.Def_OAI_Geometry_DoublingHilbert_Derivatives

-- ---- from OAI.Geometry.DoublingHilbert.Derivatives ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-! Derivative fields, good points, and the compact set of derivative norms. -/

open MeasureTheory Set Filter
open scoped BigOperators Topology

open MeasureTheory Set Filter
open scoped Topology

noncomputable section
namespace DoublingHilbert

section BoundedFields
variable {E : Type*} [NormedAddCommGroup E]

/-- A measurable uniformly bounded field on the source plane is locally integrable. -/
theorem locallyIntegrable_of_uniform_bound {G : ℝ × ℝ → E}
    (hG : AEStronglyMeasurable G volume) {M : ℝ}
    (hM : 0 ≤ M) (hbound : ∀ p, ‖G p‖ ≤ M) :
    LocallyIntegrable G volume := by
  apply (locallyIntegrable_const (μ := volume) M).mono hG
  filter_upwards with p
  simpa only [Real.norm_eq_abs, abs_of_nonneg hM] using hbound p

/-- Lebesgue differentiation for bounded fields. -/
theorem ae_tendsto_average_norm_sub_sq {G : ℝ × ℝ → E}
    (hG : AEStronglyMeasurable G volume) {M : ℝ}
    (hM : 0 ≤ M) (hbound : ∀ p, ‖G p‖ ≤ M) :
    ∀ᵐ p, Tendsto (fun r : ℝ => ⨍ q in Metric.closedBall p r, ‖G q - G p‖ ^ 2)
      (𝓝[>] 0) (𝓝 0) := by
  have hloc := locallyIntegrable_of_uniform_bound hG hM hbound
  filter_upwards [IsUnifLocDoublingMeasure.ae_tendsto_average_norm_sub volume hloc (0 : ℝ)]
    with p hp
  have hlim := hp (fun _ : ℝ => p) (fun r : ℝ => r) tendsto_id
    (Eventually.of_forall fun _ => by simp)
  have hdiff (q : ℝ × ℝ) : ‖G q - G p‖ ≤ 2 * M :=
    (norm_sub_le _ _).trans (by linarith [hbound q, hbound p])
  have hsquareloc : LocallyIntegrable (fun q => ‖G q - G p‖ ^ 2) volume := by
    apply locallyIntegrable_of_uniform_bound
      ((hG.sub (aestronglyMeasurable_const (b := G p))).norm.pow 2) (by positivity : 0 ≤ (2 * M) ^ 2)
    intro q
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (hdiff q) 2
  have hnormloc : LocallyIntegrable (fun q => ‖G q - G p‖) volume := by
    apply locallyIntegrable_of_uniform_bound
      (hG.sub (aestronglyMeasurable_const (b := G p))).norm (by positivity : 0 ≤ 2 * M)
    intro q
    simpa only [Pi.sub_apply, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using hdiff q
  have hlim' : Tendsto
      (fun r : ℝ => (2 * M) * (⨍ q in Metric.closedBall p r, ‖G q - G p‖))
      (𝓝[>] 0) (𝓝 0) := by simpa using tendsto_const_nhds.mul hlim
  apply squeeze_zero' (Eventually.of_forall fun r => ?_) (Eventually.of_forall fun r => ?_) hlim'
  · exact integral_nonneg fun _ => sq_nonneg _
  · have hi := hnormloc.integrableOn_isCompact (isCompact_closedBall p r)
    have hisq := hsquareloc.integrableOn_isCompact (isCompact_closedBall p r)
    change (∫ q, ‖G q - G p‖ ^ 2 ∂_) ≤ 2 * M * (∫ q, ‖G q - G p‖ ∂_)
    rw [← integral_const_mul]
    exact integral_mono hisq.to_average (hi.const_mul _).to_average
      (fun q => by nlinarith [hdiff q, norm_nonneg (G q - G p)])

end BoundedFields

section DerivativeFields
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

end DerivativeFields
end DoublingHilbert

namespace DoublingHilbert
open MeasureTheory Set Filter
open scoped Topology

section Embedding
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

end Embedding
end DoublingHilbert

open Set
noncomputable section
namespace DoublingHilbert

end DoublingHilbert

end
end

end OAI

-- ---- platform node ----
open OAI OAI.DoublingHilbert
open MeasureTheory Set Filter
open scoped BigOperators Topology
open MeasureTheory Set Filter
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E]

theorem solution {G : ℝ × ℝ → E}
    (hG : AEStronglyMeasurable G volume) {M : ℝ}
    (hM : 0 ≤ M) (hbound : ∀ p, ‖G p‖ ≤ M) :
    ∀ᵐ p, Tendsto (fun r : ℝ => ⨍ q in Metric.closedBall p r, ‖G q - G p‖ ^ 2)
      (𝓝[>] 0) (𝓝 0) := by
  first
    | exact OAI.DoublingHilbert.ae_tendsto_average_norm_sub_sq hG hM hbound
    | exact OAI.DoublingHilbert.ae_tendsto_average_norm_sub_sq
    | (apply OAI.DoublingHilbert.ae_tendsto_average_norm_sub_sq <;> assumption)
    | (intros; apply OAI.DoublingHilbert.ae_tendsto_average_norm_sub_sq <;> assumption)
