-- Prove2me | solution 1 for GlobalTheory.FrameSplit.lintegral_le_of_section
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T15:31:51.122393+00:00
-- url     : https://prove2.me/submissions/9dc4e055-f632-46b3-8639-c7be00bfc3fe

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_LintegralLeOfSection

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix
open GlobalTheory GlobalTheory.FrameSplit
namespace GlobalTheory.FrameSplit
theorem _root_.solution {A B : Type*} [NormedAddCommGroup A] [NormedAddCommGroup B]
    [MeasurableSpace A] [BorelSpace A] [MeasurableSpace B] [BorelSpace B]
    [ProperSpace A] [ProperSpace B]
    (μ : Measure A) [μ.IsAddHaarMeasure] (ν : Measure B) [ν.IsAddHaarMeasure]
    (L : A → B) (hL : Continuous L) (hadd : ∀ x y, L (x + y) = L x + L y)
    (s : B → A) (hs : ∀ b, L (s b) = b) (S : Set A) (hS : MeasurableSet S)
    (hinv : ∀ b x, s b + x ∈ S ↔ x ∈ S)
    (hb : ∀ C : ℝ, ∃ D : ℝ, ∀ x ∈ S, ‖L x‖ ≤ C → ‖x‖ ≤ D) :
    ∃ K : ℝ≥0∞, K < ⊤ ∧ ∀ g : B → ℝ≥0∞, Measurable g →
      ∫⁻ y in S, g (L y) ∂μ ≤ K * ∫⁻ z, g z ∂ν := by
  have hLm : Measurable L := hL.measurable
  set ρ : Measure B := (μ.restrict S).map L with hρ
  have happ : ∀ T : Set B, MeasurableSet T → ρ T = μ (L ⁻¹' T ∩ S) := by
    intro T hT
    rw [hρ, Measure.map_apply hLm hT, Measure.restrict_apply (hLm hT)]
  haveI : IsFiniteMeasureOnCompacts ρ := by
    refine ⟨fun T hT => ?_⟩
    obtain ⟨C, hC⟩ := hT.isBounded.exists_norm_le
    obtain ⟨D, hD⟩ := hb C
    rw [happ T hT.measurableSet]
    refine lt_of_le_of_lt (measure_mono (t := Metric.closedBall 0 D) ?_)
      (isCompact_closedBall (0 : A) D).measure_lt_top
    intro x hx
    simpa using hD x hx.2 (hC _ hx.1)
  haveI : ρ.IsAddLeftInvariant := by
    refine ⟨fun b => ?_⟩
    ext T hT
    have hm : Measurable fun z : B => b + z := (continuous_const.add continuous_id).measurable
    rw [Measure.map_apply hm hT, happ _ (hm hT), happ _ hT,
      ← measure_preimage_add μ (s b) (L ⁻¹' T ∩ S)]
    congr 1
    ext x
    simp [hadd, hs, hinv]
  refine ⟨(ρ.addHaarScalarFactor ν : ℝ≥0∞), ENNReal.coe_lt_top, fun g hg => le_of_eq ?_⟩
  rw [← lintegral_map hg hLm, ← hρ]
  conv_lhs => rw [Measure.isAddLeftInvariant_eq_smul ρ ν]
  rw [lintegral_smul_measure]
  rfl
end GlobalTheory.FrameSplit
