-- Prove2me | solution 1 for OAI.BalancedTransport.Geometry.loadingVelocity_supported
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T05:55:10.105342+00:00
-- url     : https://prove2.me/submissions/2198187c-2c69-4a58-be18-70c8d60c706d

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

open OAI OAI.BalancedTransport OAI.BalancedTransport.Geometry
open scoped Topology
open Filter Set
theorem h45_curl_zero (A : Space → Space) (x : Space) (h : ∀ᶠ y in 𝓝 x, A y = 0) :
    curl A x = 0 := by
  have hk : ∀ k, (fun y => A y k) =ᶠ[𝓝 x] fun _ => (0:ℝ) := fun k => by
    filter_upwards [h] with y hy
    simp [hy]
  unfold curl pd
  rw [(hk 0).fderiv_eq, (hk 1).fderiv_eq, (hk 2).fderiv_eq]
  ext i
  fin_cases i <;> simp

theorem solution (z : Space) {η : ℝ} (hη : 0 < η) :
    SpatiallySupported (loadingSupport z η) (loadingVelocity z η) := by
  intro t x hx
  simp only [loadingSupport, mem_closedEnlargement, not_forall, not_and_or, not_le] at hx
  obtain ⟨i, hi⟩ := hx
  have hs0 : 0 ≤ loadingSwitch t := Real.smoothTransition.nonneg _
  have hs1 : loadingSwitch t ≤ 1 := Real.smoothTransition.le_one _
  let p : Space := lowerEndpoint fixedLabel (loadingCenter z) (fun _ => 1) t
  have hpi : p i = loadingSwitch t * (z i - fixedLabel i) + fixedLabel i := by
    simp [p, lowerEndpoint, loadingCenter]
  have hlo : min (fixedLabel i) (z i) ≤ p i := by
    rw [hpi]
    rcases le_total (fixedLabel i) (z i) with h | h
    · rw [min_eq_left h]; nlinarith
    · rw [min_eq_right h]; nlinarith
  have hhi : p i ≤ max (fixedLabel i) (z i) := by
    rw [hpi]
    rcases le_total (fixedLabel i) (z i) with h | h
    · rw [max_eq_right h]; nlinarith
    · rw [max_eq_left h]; nlinarith
  have hcut : ∀ᶠ y in 𝓝 x, boxCutoff p p η y = 0 := by
    rcases hi with h | h
    · have hm : {y : Space | y i < p i - 2 * η} ∈ 𝓝 x :=
        (isOpen_lt (continuous_apply i) continuous_const).mem_nhds (by show x i < p i - 2 * η; linarith)
      filter_upwards [hm] with y hy
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      rw [Real.smoothTransition.zero_of_nonpos, zero_mul]
      apply div_nonpos_of_nonpos_of_nonneg _ hη.le
      linarith
    · have hm : {y : Space | p i + 2 * η < y i} ∈ 𝓝 x :=
        (isOpen_lt continuous_const (continuous_apply i)).mem_nhds (by show p i + 2 * η < x i; linarith)
      filter_upwards [hm] with y hy
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      rw [Real.smoothTransition.zero_of_nonpos (x := (p i + 2 * η - y i) / η), mul_zero]
      apply div_nonpos_of_nonpos_of_nonneg _ hη.le
      linarith
  show localizedAffine p p _ _ _ η x = 0
  unfold localizedAffine
  apply h45_curl_zero
  filter_upwards [hcut] with y hy
  simp [hy]

