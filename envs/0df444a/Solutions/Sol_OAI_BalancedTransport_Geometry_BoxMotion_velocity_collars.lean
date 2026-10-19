-- Prove2me | solution 1 for OAI.BalancedTransport.Geometry.BoxMotion.velocity_collars
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T05:55:27.03379+00:00
-- url     : https://prove2.me/submissions/7353f2b3-b51b-456a-acad-ccae807b3e5c

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
theorem h45_vel_zero {ι : Type*} [Fintype ι] {A B : BoxLayout ι} {safe : Set ι} {η : ℝ}
    (m : BoxMotion A B safe η) (t : ℝ) (L : BoxLayout ι)
    (hL : ∀ᶠ s in 𝓝 t, m.center (2 * s - 1 / 2) = L.center ∧ m.width (2 * s - 1 / 2) = L.width) :
    m.velocity t = 0 := by
  have h1 : ∀ i, deriv (m.fieldCenter i) t = 0 := by
    intro i
    have : m.fieldCenter i =ᶠ[𝓝 t] fun _ => L.center i := by
      filter_upwards [hL] with s hs
      simp only [BoxMotion.fieldCenter]; rw [hs.1]
    rw [this.deriv_eq]; simp
  have h2 : ∀ i k, deriv (fun s => m.fieldScale i s k) t = 0 := by
    intro i k
    have : (fun s => m.fieldScale i s k) =ᶠ[𝓝 t] fun _ => L.width i k / A.width i k := by
      filter_upwards [hL] with s hs
      simp only [BoxMotion.fieldScale]; rw [hs.2]
    rw [this.deriv_eq]; simp
  have h3 : ∀ i, logarithmicRate (m.fieldScale i) t = 0 := by
    intro i; funext k; simp [logarithmicRate, h2]
  funext x
  simp [BoxMotion.velocity, familyVelocity, movingBoxVelocity, h1, h3]

theorem solution (m : BoxMotion A B safe η) : TimeCollars m.velocity := by
  intro t ht
  rcases ht with ht | ht
  · apply h45_vel_zero m t A
    filter_upwards [Iio_mem_nhds ht] with s hs
    simp only [Set.mem_Iio] at hs
    exact ⟨m.start_center _ (by linarith), m.start_width _ (by linarith)⟩
  · apply h45_vel_zero m t B
    filter_upwards [Ioi_mem_nhds ht] with s hs
    simp only [Set.mem_Ioi] at hs
    exact ⟨m.end_center _ (by linarith), m.end_width _ (by linarith)⟩

