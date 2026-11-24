-- Prove2me | solution 1 for GlobalTheory.glueMeas_univ_ne_top_of_compact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:58:56.734437+00:00
-- url     : https://prove2.me/submissions/62b8efea-d9e1-44a8-a8ff-c8b65135daff

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ChartMeasApplyOfSubset
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GlueMeasUnivNeTopOfCompact

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Set MeasureTheory
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ENNReal
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {M : Type} [TopologicalSpace M] [CompactSpace M]
    [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M] {n : ℕ} {ι : Type}
    (e : ι → OpenPartialHomeomorph M (V n)) (hcov : ∀ y, ∃ i, y ∈ (e i).source)
    (hd : ∀ i j, DifferentiableOn ℂ (e j ∘ (e i).symm)
      ((e i).target ∩ (e i).symm ⁻¹' (e j).source))
    (r : ι → V n → ℝ) (hr : ∀ i, ContinuousOn (r i) (e i).target)
    (hc : ∀ i j y, y ∈ (e i).source → y ∈ (e j).source →
      r i (e i y) = ‖GlobalTheory.ChartGlue.transDet (e i) (e j) y‖ ^ 2 * r j (e j y)) :
    GlobalTheory.ChartGlue.glueMeas e (fun i y => ENNReal.ofReal (r i (e i y))) univ ≠ ∞ := by
  classical
  set μ := GlobalTheory.ChartGlue.glueMeas e (fun i y => ENNReal.ofReal (r i (e i y))) with hμ
  have hρ : ∀ i j y, y ∈ (e i).source → y ∈ (e j).source →
      ENNReal.ofReal (r i (e i y)) =
        ENNReal.ofReal (‖GlobalTheory.ChartGlue.transDet (e i) (e j) y‖ ^ 2) * ENNReal.ofReal (r j (e j y)) := by
    intro i j y hi hj
    rw [← ENNReal.ofReal_mul (sq_nonneg _), hc i j y hi hj]
  have hloc : ∀ y : M, ∃ U : Set M, IsOpen U ∧ y ∈ U ∧ μ U < ∞ := by
    intro y
    obtain ⟨i, hi⟩ := hcov y
    have hT : (e i).target ∈ nhds ((e i) y) := (e i).open_target.mem_nhds ((e i).map_source hi)
    obtain ⟨δ, hδ, hδs⟩ := Metric.nhds_basis_closedBall.mem_iff.1 hT
    set U := (e i).source ∩ (e i) ⁻¹' Metric.ball ((e i) y) δ with hUdef
    have hUo : IsOpen U :=
      (e i).continuousOn.isOpen_inter_preimage (e i).open_source Metric.isOpen_ball
    have hUs : U ⊆ (e i).source := inter_subset_left
    have himg : (e i) '' U ⊆ Metric.closedBall ((e i) y) δ := by
      rintro _ ⟨z, hz, rfl⟩
      exact Metric.ball_subset_closedBall hz.2
    obtain ⟨C, hC⟩ :=
      (isCompact_closedBall ((e i) y) δ).exists_bound_of_continuousOn ((hr i).mono hδs)
    refine ⟨U, hUo, ⟨hi, Metric.mem_ball_self hδ⟩, ?_⟩
    have hm := GlobalTheory.ChartGlue.measurableSet_image (e i) hUo.measurableSet hUs
    rw [hμ, GlobalTheory.ChartGlue.glueMeas_apply e _ hd hρ i hUo.measurableSet hUs,
      GlobalTheory.ChartGlue.chartMeas_apply_of_subset _ _ hUo.measurableSet hUs]
    calc ∫⁻ v in (e i) '' U, ENNReal.ofReal (r i ((e i) ((e i).symm v)))
        ≤ ∫⁻ _ in (e i) '' U, ENNReal.ofReal C := by
          refine setLIntegral_mono' hm fun v hv => ENNReal.ofReal_le_ofReal ?_
          rw [(e i).right_inv (hδs (himg hv))]
          have := hC v (himg hv)
          rw [Real.norm_eq_abs] at this
          exact (le_abs_self _).trans this
      _ = ENNReal.ofReal C * volume ((e i) '' U) := setLIntegral_const _ _
      _ ≤ ENNReal.ofReal C * volume (Metric.closedBall ((e i) y) δ) := by
          gcongr
      _ < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top measure_closedBall_lt_top
  choose U hUo hyU hUf using hloc
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover U hUo
    (fun y _ => mem_iUnion.2 ⟨y, hyU y⟩)
  refine ne_of_lt (lt_of_le_of_lt (measure_mono ht) ?_)
  exact (measure_biUnion_finset_le t U).trans_lt (ENNReal.sum_lt_top.2 fun y _ => hUf y)
end GlobalTheory
