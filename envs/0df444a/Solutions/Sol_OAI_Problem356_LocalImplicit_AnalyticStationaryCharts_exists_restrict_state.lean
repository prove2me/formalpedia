-- Prove2me | solution 1 for OAI.Problem356.LocalImplicit.AnalyticStationaryCharts.exists_restrict_state
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T21:41:59.268265+00:00
-- url     : https://prove2.me/submissions/5faa04c1-2f12-4d52-bf80-46ca3a611f28

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

open OAI OAI.Problem356 OAI.Problem356.LocalImplicit OAI.Problem356.LocalImplicit.AnalyticStationaryCharts
universe uP uS
open Filter Set
open scoped Topology ContDiff
variable {P : Type uP} {S : Type uS}
  [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]
  [NormedAddCommGroup S] [NormedSpace ℝ S] [CompleteSpace S]
variable {G : P × (S × S) → S × S} {p : P} {s : S × S}


omit [CompleteSpace P] [CompleteSpace S]
theorem solution
    (c : AnalyticStationaryCharts G p s) (W : Set (S × S))
    (hW : IsOpen W) (hsW : s ∈ W) (hWV : W ⊆ c.stateDomain) :
    ∃ d : AnalyticStationaryCharts G p s,
      d.stateDomain = W ∧ d.central.source ⊆ c.central.source ∧
      (d.central : P → S) = c.central ∧ (d.opposite : P → S) = c.opposite := by
  set U : Set P := c.central.source ∩ (fun y => (c.central y, c.opposite y)) ⁻¹' W with hUdef
  have hcont : ContinuousOn (fun y => (c.central y, c.opposite y)) c.central.source :=
    c.central.continuousOn.prodMk (c.source_eq ▸ c.opposite.continuousOn)
  have hU : IsOpen U := hcont.isOpen_inter_preimage c.central.open_source hW
  have hUs : U ⊆ c.central.source := fun y hy => hy.1
  have hUs' : U ⊆ c.opposite.source := c.source_eq ▸ hUs
  have hsrc : (c.central.restrOpen U hU).source = U := by
    rw [OpenPartialHomeomorph.restrOpen_source]; exact Set.inter_eq_right.mpr hUs
  have hsrc' : (c.opposite.restrOpen U hU).source = U := by
    rw [OpenPartialHomeomorph.restrOpen_source]; exact Set.inter_eq_right.mpr hUs'
  refine ⟨{
    central := c.central.restrOpen U hU
    opposite := c.opposite.restrOpen U hU
    source_eq := by rw [hsrc, hsrc']
    point_mem := by
      rw [hsrc]
      refine ⟨c.point_mem, ?_⟩
      show (c.central p, c.opposite p) ∈ W
      rw [c.central_value, c.opposite_value]; exact hsW
    central_value := c.central_value
    opposite_value := c.opposite_value
    stateDomain := W
    stateDomain_open := hW
    state_mem := hsW
    mapsTo_state := by
      rw [hsrc]; intro y hy; exact hy.2
    stationary := by
      rw [hsrc]; intro y hy; exact c.stationary y hy.1
    unique_zero := by
      rw [hsrc]; intro y hy z hz; exact c.unique_zero y hy.1 z (hWV hz)
    central_analytic := by
      rw [hsrc]; exact c.central_analytic.mono hUs
    central_inverse_analytic := c.central_inverse_analytic.mono fun y hy => hy.1
    opposite_analytic := by
      rw [hsrc']; exact c.opposite_analytic.mono hUs'
    opposite_inverse_analytic := c.opposite_inverse_analytic.mono fun y hy => hy.1 }, rfl, ?_, rfl, rfl⟩
  show (c.central.restrOpen U hU).source ⊆ c.central.source
  rw [hsrc]; exact hUs

