-- Prove2me | solution 1 for OAI.NoiselessRegression.map_apply_open_le_of_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T10:11:32.560587+00:00
-- url     : https://prove2.me/submissions/ef2d44fc-0619-4f8c-8f36-95802e07dc37

-- Generated from openai/math@1581d4c lean/OAI/Probability/GaussianRegression/Smoothing.lean:L171-L205
-- (upload_full_project.md Phase 4): solution for node OAI.NoiselessRegression.map_apply_open_le_of_tendsto. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_NoiselessRegression
import Definitions.Def_OAI_Probability_ProjectionMoments_Model
import Definitions.Def_OAI_Probability_GaussianRegression_Nets
import Definitions.Def_OAI_Probability_GaussianRegression_Gram
import Definitions.Def_OAI_Probability_GaussianRegression_ReplicaMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Smoothing

-- ---- from OAI.Probability.GaussianRegression.Smoothing ----
namespace OAI

/-!
Projection smoothing, Gaussian noise, and bounds under weak limits.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open InnerProductSpace

noncomputable section

universe u

namespace NoiselessRegression

section SmoothingMoments
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

end SmoothingMoments

section ProductDensity
variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ]

end ProductDensity

section HolderSet
variable {X : Type*} [MeasurableSpace X] (μ : Measure X)
end HolderSet

section LimitSet
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [TopologicalSpace Y] [BorelSpace Y]
  (ρ : Measure X) (τ : Measure Y)

lemma map_apply_open_le_of_tendsto (F : X → Y) (Fₖ : ℕ → X → Y)
    (hF : Measurable F) (hFₖ : ∀ k, Measurable (Fₖ k))
    (ht : ∀ x, Tendsto (fun k => Fₖ k x) atTop (𝓝 (F x)))
    (C : ℝ≥0∞) (α : ℝ)
    (hbound : ∀ k U, IsOpen U → (ρ.map (Fₖ k)) U ≤ C * (τ U)^α)
    (U : Set Y) (hU : IsOpen U) :
    (ρ.map F) U ≤ C * (τ U)^α := by
  let f : ℕ → X → ℝ≥0∞ := fun k => (Fₖ k ⁻¹' U).indicator (fun _ => 1)
  have hf : ∀ k, Measurable (f k) := fun k =>
    measurable_const.indicator (hU.measurableSet.preimage (hFₖ k))
  have hind : ∀ x, (F ⁻¹' U).indicator (fun _ => (1 : ℝ≥0∞)) x ≤
      atTop.liminf (fun k => f k x) := by
    intro x
    by_cases hx : F x ∈ U
    · rw [Set.indicator_of_mem (show x ∈ F ⁻¹' U from hx)]
      apply le_liminf_of_le (by isBoundedDefault)
      filter_upwards [(ht x).eventually (hU.mem_nhds hx)] with k hk
      change 1 ≤ (Fₖ k ⁻¹' U).indicator (fun _ => (1 : ℝ≥0∞)) x
      rw [Set.indicator_of_mem (show x ∈ Fₖ k ⁻¹' U from hk)]
    · rw [Set.indicator_of_notMem (show x ∉ F ⁻¹' U from hx)]
      exact zero_le
  calc
    (ρ.map F) U = ∫⁻ x, (F ⁻¹' U).indicator (fun _ => (1 : ℝ≥0∞)) x ∂ρ := by
      rw [Measure.map_apply hF hU.measurableSet,
        lintegral_indicator (hU.measurableSet.preimage hF)]
      simp
    _ ≤ ∫⁻ x, atTop.liminf (fun k => f k x) ∂ρ := lintegral_mono hind
    _ ≤ atTop.liminf (fun k => ∫⁻ x, f k x ∂ρ) := lintegral_liminf_le hf
    _ ≤ _ := by
      apply liminf_le_of_frequently_le (hu_le := by isBoundedDefault)
      apply Filter.Eventually.frequently
      filter_upwards [] with k
      have hk := hbound k U hU
      simpa [f, lintegral_indicator (hU.measurableSet.preimage (hFₖ k)),
        Measure.map_apply (hFₖ k) hU.measurableSet] using hk
end LimitSet

variable {Y : Type*} [MeasurableSpace Y] [TopologicalSpace Y]

end NoiselessRegression

end

end OAI

-- ---- platform node ----
open OAI OAI.NoiselessRegression
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open InnerProductSpace


theorem solution : type_of% @_root_.OAI.NoiselessRegression.map_apply_open_le_of_tendsto := @_root_.OAI.NoiselessRegression.map_apply_open_le_of_tendsto
