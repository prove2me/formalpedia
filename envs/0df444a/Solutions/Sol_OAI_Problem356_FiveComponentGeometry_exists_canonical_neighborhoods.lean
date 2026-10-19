-- Prove2me | solution 1 for OAI.Problem356.FiveComponentGeometry.exists_canonical_neighborhoods
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T22:34:42.009627+00:00
-- url     : https://prove2.me/submissions/8a4a37b2-3960-45fd-9b6d-93d8cbe21053

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
open scoped ENNReal
open CenterCertificate GoodTypePermutation
open scoped InnerProductSpace in
open LocalGeometry StationaryMap in
theorem h41_elc {a : E3} (C : ChartsAt a) {x y z : E3}
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


theorem h41_sep {x y c c' : E3} {r r' : ℝ} (hx : x ∈ ball c r) (hy : y ∈ ball c' r')
    (h : r + r' ≤ dist c c') : 0 < dist x y := by
  rw [Metric.mem_ball] at hx hy
  have := dist_triangle4 c x y c'
  rw [dist_comm c x] at this
  linarith

theorem h41_pt_dist (a b : Fin 5) (h : a ≠ b) : 1 ≤ dist (point a) (point b) := by
  rw [dist_eq_norm]
  fin_cases a <;> fin_cases b <;> simp [point, EuclideanSpace.norm_eq, Fin.sum_univ_three] at h ⊢ <;>
    norm_num [Real.le_sqrt]

theorem h41_p2' : point 2 = -point 1 := by
  ext i; fin_cases i <;> simp [point]

theorem h41_p4' : point 4 = -point 3 := by
  ext i; fin_cases i <;> simp [point]

theorem h41_p0' : point 0 = 0 := by
  ext i; fin_cases i <;> simp [point]

theorem solution
    (C₁ : ChartsAt (point 1)) (C₂ : ChartsAt (point 3)) :
    ∃ W : Fin 5 → Set E3,
      (∀ i, W i ∈ nhds (point i)) ∧
      LocalTypeCertificate W (potentials C₁ C₂) (branchContact C₁ C₂) 0 1 2 ∧
      LocalTypeCertificate W (potentials C₁ C₂) (branchContact C₁ C₂) 0 3 4 := by
  set r0 := min (min C₁.stateRadius C₂.stateRadius) (1 / 3 : ℝ) with hr0
  set r1 := min C₁.parameterRadius (1 / 3 : ℝ) with hr1
  set r2 := min C₁.stateRadius (1 / 3 : ℝ) with hr2
  set r3 := min C₂.parameterRadius (1 / 3 : ℝ) with hr3
  set r4 := min C₂.stateRadius (1 / 3 : ℝ) with hr4
  have p0 : 0 < r0 := lt_min (lt_min C₁.stateRadius_pos C₂.stateRadius_pos) (by norm_num)
  have p1 : 0 < r1 := lt_min C₁.parameterRadius_pos (by norm_num)
  have p2 : 0 < r2 := lt_min C₁.stateRadius_pos (by norm_num)
  have p3 : 0 < r3 := lt_min C₂.parameterRadius_pos (by norm_num)
  have p4 : 0 < r4 := lt_min C₂.stateRadius_pos (by norm_num)
  have l0 : r0 ≤ 1 / 3 := min_le_right _ _
  have l1 : r1 ≤ 1 / 3 := min_le_right _ _
  have l2 : r2 ≤ 1 / 3 := min_le_right _ _
  have l3 : r3 ≤ 1 / 3 := min_le_right _ _
  have l4 : r4 ≤ 1 / 3 := min_le_right _ _
  have d01 := h41_pt_dist 0 1 (by decide)
  have d02 := h41_pt_dist 0 2 (by decide)
  have d12 := h41_pt_dist 1 2 (by decide)
  have d03 := h41_pt_dist 0 3 (by decide)
  have d04 := h41_pt_dist 0 4 (by decide)
  have d34 := h41_pt_dist 3 4 (by decide)
  refine ⟨![ball (point 0) r0, ball (point 1) r1, ball (point 2) r2, ball (point 3) r3,
    ball (point 4) r4], ?_, ?_, ?_⟩
  · intro i
    fin_cases i
    · exact ball_mem_nhds _ p0
    · exact ball_mem_nhds _ p1
    · exact ball_mem_nhds _ p2
    · exact ball_mem_nhds _ p3
    · exact ball_mem_nhds _ p4
  · intro x hx y hy z hz
    change x ∈ ball (point 0) r0 at hx
    change y ∈ ball (point 1) r1 at hy
    change z ∈ ball (point 2) r2 at hz
    have hxy := h41_sep hx hy (by linarith)
    have hxz := h41_sep hx hz (by linarith)
    have hyz := h41_sep hy hz (by linarith)
    have hy' : y ∈ ball (point 1) C₁.parameterRadius := Metric.ball_subset_ball (min_le_left _ _) hy
    have hx' : x ∈ ball (0 : E3) C₁.stateRadius := by
      have := Metric.ball_subset_ball (x := point 0) ((min_le_left _ _).trans (min_le_left _ _)) hx
      rwa [h41_p0'] at this
    have hz' : z ∈ ball (-point 1) C₁.stateRadius := by
      have := Metric.ball_subset_ball (min_le_left _ _) hz
      rwa [h41_p2'] at this
    have H := h41_elc C₁ hy' hx' hz' hxy hxz hyz
    refine ⟨H.1, fun he => ?_⟩
    obtain ⟨e1, e2⟩ := H.2.mp he
    refine Or.inl ⟨y, ?_, ?_⟩
    · rw [C₁.source_ball]; exact hy'
    · rw [e1, e2]
  · intro x hx y hy z hz
    change x ∈ ball (point 0) r0 at hx
    change y ∈ ball (point 3) r3 at hy
    change z ∈ ball (point 4) r4 at hz
    have hxy := h41_sep hx hy (by linarith)
    have hxz := h41_sep hx hz (by linarith)
    have hyz := h41_sep hy hz (by linarith)
    have hy' : y ∈ ball (point 3) C₂.parameterRadius := Metric.ball_subset_ball (min_le_left _ _) hy
    have hx' : x ∈ ball (0 : E3) C₂.stateRadius := by
      have := Metric.ball_subset_ball (x := point 0) ((min_le_left _ _).trans (min_le_right _ _)) hx
      rwa [h41_p0'] at this
    have hz' : z ∈ ball (-point 3) C₂.stateRadius := by
      have := Metric.ball_subset_ball (min_le_left _ _) hz
      rwa [h41_p4'] at this
    have H := h41_elc C₂ hy' hx' hz' hxy hxz hyz
    refine ⟨H.1, fun he => ?_⟩
    obtain ⟨e1, e2⟩ := H.2.mp he
    refine Or.inr ⟨y, ?_, ?_⟩
    · rw [C₂.source_ball]; exact hy'
    · rw [e1, e2]

