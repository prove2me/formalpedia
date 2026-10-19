-- Prove2me | solution 1 for OAI.BalancedTransport.Geometry.BoxMotion.velocity_compact_support
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T05:55:52.317605+00:00
-- url     : https://prove2.me/submissions/b588e1ea-29d7-4caf-8110-726c024ebaf7

import Mathlib
import Definitions.Def_BalancedThreeStack
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_FlatBounds
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_EffectiveArithmetic
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_RationalAlgorithms
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_EffectiveExp
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_RecorderRules
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_PrefixCoding
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_BoxCoding
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Work
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_TimeRegularity
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_FieldBounds
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_CompactFamilies
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_ResidualRegularity
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_RhoAlgorithms
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_EffectiveLog
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_NumericPrograms
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_ComputabilityRules
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_MachineRecursion
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_FiniteSimulator
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_UniversalInput
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_NumericBounds
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_NumericEvaluation
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_NumericDifferentiation
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_NumericScopes
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_NumericJets
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_NumericAlgebra
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Elementary
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_EnergyCurve
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Sobolev
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_EnergySlice
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Loading
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Periodic
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Motion
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Parking
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Deformation
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_ElementaryMotion
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_ElementaryCalculus
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_RecorderSimulation
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_MachineHalting
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Bridge
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_MotionField

open OAI OAI.BalancedTransport OAI.BalancedTransport.Geometry OAI.BalancedTransport.Geometry.BoxMotion
open Set Filter
open scoped Topology
variable {ι : Type*} [Fintype ι]
variable {A B : BoxLayout ι} {safe : Set ι} {η : ℝ}
theorem h45_curl_zero (A : Space → Space) (x : Space) (h : ∀ᶠ y in 𝓝 x, A y = 0) :
    curl A x = 0 := by
  have hk : ∀ k, (fun y => A y k) =ᶠ[𝓝 x] fun _ => (0:ℝ) := fun k => by
    filter_upwards [h] with y hy
    simp [hy]
  unfold curl pd
  rw [(hk 0).fderiv_eq, (hk 1).fderiv_eq, (hk 2).fderiv_eq]
  ext i
  fin_cases i <;> simp

theorem h45_bound {ι : Type*} [Fintype ι] (f : ℝ → ι → Space) (hf : Continuous f)
    (h0 : ∀ s, s ≤ 0 → f s = f 0) (h1 : ∀ s, 1 ≤ s → f s = f 1) :
    ∃ C, 0 ≤ C ∧ ∀ s i k, |f s i k| ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0:ℝ)) (b := 1)).exists_bound_of_continuousOn hf.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun s i k => ?_⟩
  have hs : ‖f s‖ ≤ C := by
    rcases le_total s 0 with h | h
    · rw [h0 s h]; exact hC 0 ⟨le_rfl, zero_le_one⟩
    · rcases le_total s 1 with h' | h'
      · exact hC s ⟨h, h'⟩
      · rw [h1 s h']; exact hC 1 ⟨zero_le_one, le_rfl⟩
  have : |f s i k| ≤ ‖f s‖ := by
    rw [← Real.norm_eq_abs]
    exact (norm_le_pi_norm (f s i) k).trans (norm_le_pi_norm (f s) i)
  linarith [le_max_left C 0]

theorem solution (m : BoxMotion A B safe η) (hη : 0 < η) :
    ∃ K : Set Space, IsCompact K ∧ SpatiallySupported K m.velocity := by
  obtain ⟨Cc, hCc0, hCc⟩ := h45_bound m.center m.smooth_center.continuous
    (fun s hs => by rw [m.start_center s hs, m.start_center 0 le_rfl])
    (fun s hs => by rw [m.end_center s hs, m.end_center 1 le_rfl])
  obtain ⟨Cw, hCw0, hCw⟩ := h45_bound m.width m.smooth_width.continuous
    (fun s hs => by rw [m.start_width s hs, m.start_width 0 le_rfl])
    (fun s hs => by rw [m.end_width s hs, m.end_width 1 le_rfl])
  have hAw : ∀ i k, 0 < A.width i k := by
    intro i k; have := m.positive 0 i k; rwa [m.start_width 0 le_rfl] at this
  have hR : 0 ≤ Cc + Cw + 2 * η := by linarith
  refine ⟨Metric.closedBall 0 (Cc + Cw + 2 * η), isCompact_closedBall _ _, ?_⟩
  intro t x hx
  rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg hR] at hx
  push_neg at hx
  obtain ⟨k, hk⟩ := hx
  rw [Real.norm_eq_abs] at hk
  simp only [BoxMotion.velocity, familyVelocity, movingBoxVelocity]
  apply Finset.sum_eq_zero
  intro i _
  unfold localizedAffine
  apply h45_curl_zero
  have hne := (hAw i k).ne'
  have hlo : lowerEndpoint (-A.width i) (m.fieldCenter i) (m.fieldScale i) t k =
      m.center (2*t - 1/2) i k - m.width (2*t-1/2) i k := by
    simp only [lowerEndpoint, BoxMotion.fieldCenter, BoxMotion.fieldScale, Pi.neg_apply]
    rw [mul_neg, div_mul_cancel₀ _ hne]; ring
  have hhi : lowerEndpoint (A.width i) (m.fieldCenter i) (m.fieldScale i) t k =
      m.center (2*t - 1/2) i k + m.width (2*t-1/2) i k := by
    simp only [lowerEndpoint, BoxMotion.fieldCenter, BoxMotion.fieldScale]
    rw [div_mul_cancel₀ _ hne]
  have hc := abs_le.mp (hCc (2*t-1/2) i k)
  have hw := abs_le.mp (hCw (2*t-1/2) i k)
  have hcut : ∀ᶠ y in 𝓝 x, boxCutoff (lowerEndpoint (-A.width i) (m.fieldCenter i) (m.fieldScale i) t)
      (lowerEndpoint (A.width i) (m.fieldCenter i) (m.fieldScale i) t) η y = 0 := by
    rcases lt_abs.mp hk with h | h
    · have hm : {y : Space | Cc + Cw + 2 * η < y k} ∈ 𝓝 x :=
        (isOpen_lt continuous_const (continuous_apply k)).mem_nhds h
      filter_upwards [hm] with y hy
      apply Finset.prod_eq_zero (Finset.mem_univ k)
      rw [Real.smoothTransition.zero_of_nonpos
        (x := (lowerEndpoint (A.width i) (m.fieldCenter i) (m.fieldScale i) t k + 2 * η - y k) / η),
        mul_zero]
      apply div_nonpos_of_nonpos_of_nonneg _ hη.le
      rw [hhi]; linarith
    · have hm : {y : Space | y k < -(Cc + Cw + 2 * η)} ∈ 𝓝 x :=
        (isOpen_lt (continuous_apply k) continuous_const).mem_nhds (by show x k < _; linarith)
      filter_upwards [hm] with y hy
      apply Finset.prod_eq_zero (Finset.mem_univ k)
      rw [Real.smoothTransition.zero_of_nonpos, zero_mul]
      apply div_nonpos_of_nonpos_of_nonneg _ hη.le
      rw [hlo]; linarith
  filter_upwards [hcut] with y hy
  simp [hy]

