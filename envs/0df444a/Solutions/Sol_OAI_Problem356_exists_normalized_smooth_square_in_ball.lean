-- Prove2me | solution 1 for OAI.Problem356.exists_normalized_smooth_square_in_ball
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T21:44:47.441769+00:00
-- url     : https://prove2.me/submissions/8084809c-3d54-4aa5-9de6-68efecf91f48

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

open OAI OAI.Problem356
open MeasureTheory
open scoped ENNReal


theorem solution (c : E3) {r : ℝ} (hr : 0 < r) :
    ∃ g : E3 → ℝ,
      (∀ x, 0 ≤ g x) ∧
      ContDiff ℝ (↑(⊤ : ENat) : WithTop ENat) g ∧
      HasCompactSupport g ∧
      tsupport g ⊆ Metric.ball c r ∧
      (∫ x : E3, (g x) ^ 2 ∂(volume : Measure E3)) = 1 := by
  let f : ContDiffBump c := ⟨r/4, r/2, by positivity, by linarith⟩
  set I := ∫ x : E3, (f x) ^ 2 with hI
  have hcont : Continuous fun x => (f x) ^ 2 := f.continuous.pow 2
  have hcs : HasCompactSupport fun x => (f x) ^ 2 :=
    f.hasCompactSupport.comp_left (g := fun t : ℝ => t ^ 2) (by simp)
  have hint : MeasureTheory.Integrable (fun x => (f x) ^ 2) (volume : Measure E3) :=
    hcont.integrable_of_hasCompactSupport hcs
  have hsupp : Function.support (fun x => (f x) ^ 2) = Metric.ball c (r/2) := by
    rw [← f.support_eq]; ext x; simp [Function.mem_support]
  have hIpos : 0 < I := by
    rw [hI, integral_pos_iff_support_of_nonneg (fun x => sq_nonneg _) hint, hsupp]
    exact Metric.measure_ball_pos _ _ (by positivity)
  refine ⟨fun x => (√I)⁻¹ * f x, fun x => mul_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) (f.nonneg),
    contDiff_const.mul f.contDiff, f.hasCompactSupport.mul_left, ?_, ?_⟩
  · refine (tsupport_mul_subset_right).trans ?_
    rw [f.tsupport_eq]
    exact Metric.closedBall_subset_ball (show r / 2 < r by linarith)
  · simp only [mul_pow]
    rw [integral_const_mul, inv_pow, Real.sq_sqrt hIpos.le, ← hI]
    exact inv_mul_cancel₀ hIpos.ne'

