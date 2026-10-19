-- Prove2me | solution 1 for OAI.Problem356.LocalGeometry.LocalSupportingCharts.exists_shrink
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T21:42:07.42923+00:00
-- url     : https://prove2.me/submissions/97f06b8e-725d-4282-ba2f-fa57a2515733

import Mathlib
import Definitions.Def_CoulombCounterexample
import Definitions.Def_OAI_Analysis_CoulombTransport_AxisHessian
import Definitions.Def_OAI_Analysis_CoulombTransport_BranchCoupling
import Definitions.Def_OAI_Analysis_CoulombTransport_CoulombEstimates
import Definitions.Def_OAI_Analysis_CoulombTransport_BranchSeparation
import Definitions.Def_OAI_Analysis_CoulombTransport_GraphBridge
import Definitions.Def_OAI_Analysis_CoulombTransport_DualCertificate
import Definitions.Def_OAI_Analysis_CoulombTransport_OptimalLocalization
import Definitions.Def_OAI_Analysis_CoulombTransport_Calibration
import Definitions.Def_OAI_Analysis_CoulombTransport_CertificateAttainment
import Definitions.Def_OAI_Analysis_CoulombTransport_SplitMeasure
import Definitions.Def_OAI_Analysis_CoulombTransport_PartitionLabel
import Definitions.Def_OAI_Analysis_CoulombTransport_CenterCertificate
import Definitions.Def_OAI_Analysis_CoulombTransport_CommonBranches
import Definitions.Def_OAI_Analysis_CoulombTransport_DensityMeasure
import Definitions.Def_OAI_Analysis_CoulombTransport_ComponentPotential
import Definitions.Def_OAI_Analysis_CoulombTransport_LocalImplicit
import Definitions.Def_OAI_Analysis_CoulombTransport_HessianCLM
import Definitions.Def_OAI_Analysis_CoulombTransport_CoulombCalculus
import Definitions.Def_OAI_Analysis_CoulombTransport_StationaryEquation
import Definitions.Def_OAI_Analysis_CoulombTransport_HessianMatrix
import Definitions.Def_OAI_Analysis_CoulombTransport_CoulombCoercivity
import Definitions.Def_OAI_Analysis_CoulombTransport_LocalCertificate

open OAI OAI.Problem356 OAI.Problem356.LocalGeometry
universe uE
open Set Filter
open scoped Topology ContDiff
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
open OAI OAI.Problem356 Set in
theorem ap_restrict {P : Type*} {S : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup S] [NormedSpace ℝ S]
    {G : P × (S × S) → S × S} {p : P} {s : S × S}
    (c : LocalImplicit.AnalyticStationaryCharts G p s) (U : Set P) (hU : IsOpen U) (hpU : p ∈ U)
    (hUs : U ⊆ c.central.source) (W : Set (S × S))
    (hW : IsOpen W) (hsW : s ∈ W) (hWV : W ⊆ c.stateDomain)
    (hmap : MapsTo (fun y => (c.central y, c.opposite y)) U W) :
    ∃ d : LocalImplicit.AnalyticStationaryCharts G p s, d.central.source = U ∧
      d.stateDomain = W ∧
      (d.central : P → S) = c.central ∧ (d.opposite : P → S) = c.opposite := by
  have hUs' : U ⊆ c.opposite.source := c.source_eq ▸ hUs
  have hsrc : (c.central.restrOpen U hU).source = U := by
    rw [OpenPartialHomeomorph.restrOpen_source]; exact Set.inter_eq_right.mpr hUs
  have hsrc' : (c.opposite.restrOpen U hU).source = U := by
    rw [OpenPartialHomeomorph.restrOpen_source]; exact Set.inter_eq_right.mpr hUs'
  refine ⟨{
    central := c.central.restrOpen U hU
    opposite := c.opposite.restrOpen U hU
    source_eq := by rw [hsrc, hsrc']
    point_mem := by rw [hsrc]; exact hpU
    central_value := c.central_value
    opposite_value := c.opposite_value
    stateDomain := W
    stateDomain_open := hW
    state_mem := hsW
    mapsTo_state := by rw [hsrc]; exact hmap
    stationary := by
      rw [hsrc]; intro y hy; exact c.stationary y (hUs hy)
    unique_zero := by
      rw [hsrc]; intro y hy z hz; exact c.unique_zero y (hUs hy) z (hWV hz)
    central_analytic := by
      rw [hsrc]; exact c.central_analytic.mono hUs
    central_inverse_analytic := c.central_inverse_analytic.mono fun y hy => hy.1
    opposite_analytic := by
      rw [hsrc']; exact c.opposite_analytic.mono hUs'
    opposite_inverse_analytic := c.opposite_inverse_analytic.mono fun y hy => hy.1 },
    hsrc, rfl, rfl, rfl⟩

theorem solution [CompleteSpace E]
    {F : E × (E × E) → ℝ} {G : E × (E × E) → E × E} {p : E} {s : E × E}
    (C : LocalSupportingCharts F G p s) (rp rs : ℝ) (hp : 0 < rp) (hs : 0 < rs) :
    ∃ D : LocalSupportingCharts F G p s,
      D.charts.central.source ⊆ C.charts.central.source ∩ Metric.ball p rp ∧
      D.charts.stateDomain ⊆ C.charts.stateDomain ∩ Metric.ball s rs ∧
      (D.charts.central : E → E) = C.charts.central ∧
      (D.charts.opposite : E → E) = C.charts.opposite ∧ D.value = C.value := by
  have hpo : p ∈ C.charts.opposite.source := C.charts.source_eq ▸ C.charts.point_mem
  have hcont : ContinuousAt (fun y => (C.charts.central y, C.charts.opposite y)) p :=
    (C.charts.central.continuousAt C.charts.point_mem).prodMk
      (C.charts.opposite.continuousAt hpo)
  have hps : (C.charts.central p, C.charts.opposite p) = s := by
    rw [C.charts.central_value, C.charts.opposite_value]
  set rs' := min C.stateRadius rs with hrs'
  have hrs'pos : 0 < rs' := lt_min C.stateRadius_pos hs
  obtain ⟨δ, hδ, hδmap⟩ := Metric.continuousAt_iff.mp hcont rs' hrs'pos
  set r := min (min C.parameterRadius rp) δ with hr
  have hrpos : 0 < r := lt_min (lt_min C.parameterRadius_pos hp) hδ
  have hUs : Metric.ball p r ⊆ C.charts.central.source := by
    rw [C.source_ball]
    exact Metric.ball_subset_ball ((min_le_left _ _).trans (min_le_left _ _))
  have hWs : Metric.ball s rs' ⊆ C.charts.stateDomain := by
    rw [C.state_ball]; exact Metric.ball_subset_ball (min_le_left _ _)
  have hmap : MapsTo (fun y => (C.charts.central y, C.charts.opposite y)) (Metric.ball p r)
      (Metric.ball s rs') := by
    intro y hy
    have := hδmap (lt_of_lt_of_le (Metric.mem_ball.mp hy) (min_le_right _ _))
    rw [hps] at this
    exact this
  obtain ⟨d, hdU, hdW, hdc, hdo⟩ := ap_restrict C.charts (Metric.ball p r) Metric.isOpen_ball
    (Metric.mem_ball_self hrpos) hUs (Metric.ball s rs') Metric.isOpen_ball
    (Metric.mem_ball_self hrs'pos) hWs hmap
  have hdU' : d.central.source ⊆ C.charts.central.source := hdU ▸ hUs
  have hdW' : d.stateDomain ⊆ C.charts.stateDomain := hdW ▸ hWs
  refine ⟨{
    charts := d
    parameterRadius := r
    parameterRadius_pos := hrpos
    source_ball := hdU
    stateRadius := rs'
    stateRadius_pos := hrs'pos
    state_ball := hdW
    value := C.value
    value_analytic := C.value_analytic.mono hdU'
    value_eq := fun y => by rw [C.value_eq, hdc, hdo]
    value_base := C.value_base
    supporting := fun y hy z hz => C.supporting y (hdU' hy) z (hdW' hz)
    contact := fun y hy z hz => by
      rw [C.contact y (hdU' hy) z (hdW' hz), hdc, hdo] }, ?_, ?_, hdc, hdo, rfl⟩
  · show d.central.source ⊆ _
    rw [hdU]
    exact fun y hy => ⟨hUs hy, Metric.ball_subset_ball ((min_le_left _ _).trans (min_le_right _ _)) hy⟩
  · show d.stateDomain ⊆ _
    rw [hdW]
    exact fun z hz => ⟨hWs hz, Metric.ball_subset_ball (min_le_right _ _) hz⟩

