-- Prove2me | solution 1 for OAI.Problem356.FiveComponentGeometry.ennreal_local_certificate
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T22:29:26.146988+00:00
-- url     : https://prove2.me/submissions/7f4abe1e-04f2-4059-915c-f216a71147cc

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
import Definitions.Def_OAI_Analysis_CoulombTransport_GluedCertificate
import Definitions.Def_OAI_Analysis_CoulombTransport_GoodTypePermutation
import Definitions.Def_OAI_Analysis_CoulombTransport_IsometryTransport
import Definitions.Def_OAI_Analysis_CoulombTransport_SmoothBranchMarginal
import Definitions.Def_OAI_Analysis_CoulombTransport_StateDual
import Definitions.Def_OAI_Analysis_CoulombTransport_CoulombSupportExistence
import Definitions.Def_OAI_Analysis_CoulombTransport_FiveComponentGeometry

open OAI OAI.Problem356 OAI.Problem356.FiveComponentGeometry
open Set Filter Metric
open scoped ENNReal InnerProductSpace
open LocalGeometry StationaryMap CenterCertificate


theorem solution {a : E3} (C : ChartsAt a) {x y z : E3}
    (hy : y ∈ ball a C.parameterRadius)
    (hx : x ∈ ball (0 : E3) C.stateRadius)
    (hz : z ∈ ball (-a) C.stateRadius)
    (hxy : 0 < dist x y) (hxz : 0 < dist x z) (hyz : 0 < dist y z) :
    ENNReal.ofReal (((5 : ℝ) / 2 - 10 * ‖x‖ ^ 2) + C.value y +
      ((5 : ℝ) / 4 * ⟪a, z + a⟫_ℝ - 10 * ‖z + a‖ ^ 2)) ≤ coulombCost (x, (y, z)) ∧
    (ENNReal.ofReal (((5 : ℝ) / 2 - 10 * ‖x‖ ^ 2) + C.value y +
      ((5 : ℝ) / 4 * ⟪a, z + a⟫_ℝ - 10 * ‖z + a‖ ^ 2)) = coulombCost (x, (y, z)) ↔
      x = C.charts.central y ∧ z = C.charts.opposite y) := by
  have hsrc : y ∈ C.charts.central.source := by rw [C.source_ball]; exact hy
  have hst : (x, z) ∈ C.charts.stateDomain := by
    rw [C.state_ball, Metric.mem_ball, Prod.dist_eq]
    exact max_lt (Metric.mem_ball.mp hx) (Metric.mem_ball.mp hz)
  have hsup := C.supporting y hsrc (x, z) hst
  have hcon := C.contact y hsrc (x, z) hst
  rw [dist_eq_norm] at hxy hxz hyz
  have hzy : 0 < ‖z - y‖ := by rw [norm_sub_rev]; exact hyz
  set R : ℝ := ‖x - y‖⁻¹ + ‖x - z‖⁻¹ + ‖z - y‖⁻¹ with hRdef
  have hRpos : 0 < R := by positivity
  have hR : coulombCost (x, (y, z)) = ENNReal.ofReal R := by
    simp only [coulombCost, invDistance, tripleFst, tripleSnd, tripleThd]
    rw [hRdef, ENNReal.ofReal_add (by positivity) (by positivity),
      ENNReal.ofReal_add (by positivity) (by positivity),
      ENNReal.ofReal_inv_of_pos hxy, ENNReal.ofReal_inv_of_pos hxz, norm_sub_rev y z,
      ENNReal.ofReal_inv_of_pos hzy]
  have hF : jointPotential a (y, (x, z)) = R - ((5 : ℝ) / 2 - 10 * ‖x‖ ^ 2) -
      ((5 : ℝ) / 4 * ⟪a, z + a⟫_ℝ - 10 * ‖z + a‖ ^ 2) := by
    simp only [jointPotential, statePotential, CoulombCalculus.pairCost, hRdef]
  rw [hF] at hsup hcon
  rw [hR]
  refine ⟨ENNReal.ofReal_le_ofReal (by linarith), ?_⟩
  constructor
  · intro h
    have hL : 0 ≤ ((5 : ℝ) / 2 - 10 * ‖x‖ ^ 2) + C.value y +
        ((5 : ℝ) / 4 * ⟪a, z + a⟫_ℝ - 10 * ‖z + a‖ ^ 2) := by
      by_contra hneg
      rw [ENNReal.ofReal_of_nonpos (not_le.mp hneg).le] at h
      exact (ENNReal.ofReal_pos.mpr hRpos).ne h
    rw [ENNReal.ofReal_eq_ofReal_iff hL hRpos.le] at h
    have := hcon.mp (by linarith)
    exact Prod.mk.injEq _ _ _ _ ▸ this
  · rintro ⟨rfl, rfl⟩
    have := hcon.mpr rfl
    congr 1
    linarith

