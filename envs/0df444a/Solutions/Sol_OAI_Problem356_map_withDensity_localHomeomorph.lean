-- Prove2me | solution 1 for OAI.Problem356.map_withDensity_localHomeomorph
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T22:24:04.934721+00:00
-- url     : https://prove2.me/submissions/567dab23-2f30-44b0-8714-a01c225db216

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
import Definitions.Def_OAI_Analysis_CoulombTransport_StationaryMap
import Definitions.Def_OAI_Analysis_CoulombTransport_LocalBranchMeasure
import Definitions.Def_OAI_Analysis_CoulombTransport_SmoothPushforward

open OAI OAI.Problem356
open MeasureTheory Set Filter
open scoped Topology ENNReal
open OAI OAI.Problem356 MeasureTheory in
theorem h41_mwd (e : OpenPartialHomeomorph E3 E3) (w : E3 → ENNReal)
    (D : E3 → E3 →L[ℝ] E3)
    (hD : ∀ y ∈ e.target, HasFDerivAt e.symm (D y) y) :
    Measure.map e (((volume : Measure E3).restrict e.source).withDensity w) =
      ((volume : Measure E3).restrict e.target).withDensity
        (fun y => ENNReal.ofReal |(D y).det| * w (e.symm y)) := by
  have hae : AEMeasurable e (((volume : Measure E3).restrict e.source).withDensity w) := by
    have : AEMeasurable e ((volume : Measure E3).restrict e.source) :=
      e.continuousOn.aemeasurable e.open_source.measurableSet
    exact this.mono_ac (withDensity_absolutelyContinuous _ _)
  ext A hA
  rw [Measure.map_apply_of_aemeasurable hae hA, withDensity_apply' _ _, withDensity_apply _ hA,
    Measure.restrict_restrict' e.open_source.measurableSet,
    Measure.restrict_restrict' e.open_target.measurableSet]
  have hs : MeasurableSet (e.target ∩ A) := e.open_target.measurableSet.inter hA
  have himg : e.symm '' (e.target ∩ A) = e ⁻¹' A ∩ e.source := by
    exact (e.toPartialEquiv.symm_image_target_inter_eq' A).trans (Set.inter_comm _ _)
  have hcv := lintegral_image_eq_lintegral_abs_det_fderiv_mul (volume : Measure E3) hs
    (f := e.symm) (f' := D)
    (fun y hy => (hD y hy.1).hasFDerivWithinAt) (e.symm.injOn.mono Set.inter_subset_left) w
  rw [himg] at hcv
  rw [hcv, Set.inter_comm]

theorem solution
    (e : OpenPartialHomeomorph E3 E3) (w : E3 → ℝ≥0∞)
    (D : E3 → E3 →L[ℝ] E3)
    (hD : ∀ y ∈ e.target, HasFDerivAt e.symm (D y) y) :
    Measure.map e (((volume : Measure E3).restrict e.source).withDensity w) =
      ((volume : Measure E3).restrict e.target).withDensity
        (fun y => ENNReal.ofReal |(D y).det| * w (e.symm y)) := by
  exact h41_mwd e w D hD

