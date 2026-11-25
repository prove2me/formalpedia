-- Prove2me | solution 1 for GlobalTheory.measure_ball_eq_lintegral_upperDens
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:28:13.37952+00:00
-- url     : https://prove2.me/submissions/fe3c7f84-e267-4253-a015-541e4b7bf17e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_UpperDens
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MeasureBallEqLintegralUpperMeasureDensity

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology
open scoped ENNReal NNReal
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (l ν : Measure V) [l.IsAddHaarMeasure] [IsFiniteMeasure ν] (η : ℝ) (C : ℝ≥0), (∀ x : V, ‖x‖ < η → GlobalTheory.HaarDensChart.upperDens l ν x < C) → ∀ ρ : ℝ, ρ ≤ η → ν (Metric.ball 0 ρ) = ∫⁻ x in Metric.ball 0 ρ, GlobalTheory.HaarDensChart.upperDens l ν x ∂l := by
  intro V _ _ _ _ _ l ν _ _ η C hC ρ hρ
  set U : Set V := Metric.ball (0 : V) η with hUdef
  have hUo : IsOpen U := Metric.isOpen_ball

  have key : ∀ x ∈ U, ∀ᶠ r in 𝓝[>] (0 : ℝ),
      ν (Metric.closedBall x r) ≤ ((C : ℝ≥0) • l) (Metric.closedBall x r) := by
    intro x hx
    have h0 : limsup (fun r : ℝ => ν (Metric.closedBall x r) / l (Metric.closedBall x r))
        (𝓝[>] (0 : ℝ)) < (C : ℝ≥0∞) := hC x (mem_ball_zero_iff.1 hx)
    filter_upwards [Filter.eventually_lt_of_limsup_lt h0, self_mem_nhdsWithin] with r hr hr0
    have hpos : l (Metric.closedBall x r) ≠ 0 := (Metric.measure_closedBall_pos l x hr0).ne'
    have hfin : l (Metric.closedBall x r) ≠ ⊤ := measure_closedBall_lt_top.ne
    rw [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
    exact ((ENNReal.div_lt_iff (Or.inl hpos) (Or.inl hfin)).1 hr).le

  have hle : ∀ s ⊆ U, ν s ≤ ((C : ℝ≥0) • l) s := fun s hs =>
    (Besicovitch.vitaliFamily ν).measure_le_of_frequently_le ((C : ℝ≥0) • l)
      Measure.AbsolutelyContinuous.rfl s
      (fun x hx => (Besicovitch.tendsto_filterAt ν x).frequently (key x (hs hx)).frequently)
  have hac : ν.restrict U ≪ l := by
    intro s hs
    rw [Measure.restrict_apply' hUo.measurableSet]
    refine le_antisymm ?_ (by simp)
    calc ν (s ∩ U) ≤ ((C : ℝ≥0) • l) (s ∩ U) := hle _ Set.inter_subset_right
      _ ≤ ((C : ℝ≥0) • l) s := measure_mono Set.inter_subset_left
      _ = 0 := by simp [hs]

  have hae : ∀ᵐ x ∂l, x ∈ U →
      GlobalTheory.HaarDensChart.upperDens l ν x = (ν.restrict U).rnDeriv l x := by
    filter_upwards [Besicovitch.ae_tendsto_rnDeriv (ν.restrict U) l] with x hx hxU
    have hev : (fun r : ℝ => ν.restrict U (Metric.closedBall x r) / l (Metric.closedBall x r))
        =ᶠ[𝓝[>] (0 : ℝ)] (fun r : ℝ => ν (Metric.closedBall x r) / l (Metric.closedBall x r)) := by
      obtain ⟨ε, εpos, hε⟩ := Metric.isOpen_iff.1 hUo x hxU
      filter_upwards [Ioo_mem_nhdsGT εpos] with r hr
      rw [Measure.restrict_eq_self _ ((Metric.closedBall_subset_ball hr.2).trans hε)]
    show limsup (fun r : ℝ => ν (Metric.closedBall x r) / l (Metric.closedBall x r))
        (𝓝[>] (0 : ℝ)) = _
    exact (hx.congr' hev).limsup_eq
  have hsub : Metric.ball (0 : V) ρ ⊆ U := Metric.ball_subset_ball hρ
  calc ν (Metric.ball 0 ρ) = ν.restrict U (Metric.ball 0 ρ) :=
        (Measure.restrict_eq_self _ hsub).symm
    _ = l.withDensity ((ν.restrict U).rnDeriv l) (Metric.ball 0 ρ) := by
        rw [Measure.withDensity_rnDeriv_eq _ _ hac]
    _ = ∫⁻ x in Metric.ball 0 ρ, (ν.restrict U).rnDeriv l x ∂l :=
        withDensity_apply _ Metric.isOpen_ball.measurableSet
    _ = ∫⁻ x in Metric.ball 0 ρ, GlobalTheory.HaarDensChart.upperDens l ν x ∂l := by
        refine setLIntegral_congr_fun_ae Metric.isOpen_ball.measurableSet ?_
        filter_upwards [hae] with x hx hxρ
        exact (hx (hsub hxρ)).symm
end GlobalTheory
