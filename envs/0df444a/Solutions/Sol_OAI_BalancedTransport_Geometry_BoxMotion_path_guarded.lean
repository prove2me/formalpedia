-- Prove2me | solution 1 for OAI.BalancedTransport.Geometry.BoxMotion.path_guarded
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T05:50:47.784688+00:00
-- url     : https://prove2.me/submissions/bf0d7bc4-0c8a-4610-8716-0cb5b93efb6e

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


theorem solution (m : BoxMotion A B safe η) {i : ι} (hi : i ∈ safe)
    {x : Space} (hx : x ∈ A.solid i) (t : ℝ) : m.path i x t ∉ observer := by
  intro hobs
  simp only [observer, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Ioo] at hobs
  have h0 := (hobs 0).2
  have hg : 2 < m.center (2 * t - 1 / 2) i 0 - m.width (2 * t - 1 / 2) i 0 :=
    m.guard (2 * t - 1 / 2) i hi
  have hA : 0 < A.width i 0 := by
    have := m.positive 0 i 0
    rwa [m.start_width 0 le_rfl] at this
  have hW : 0 < m.width (2 * t - 1 / 2) i 0 := m.positive _ _ _
  simp only [BoxLayout.solid, Set.mem_Icc, Pi.le_def, Pi.sub_apply, Pi.add_apply] at hx
  have hx1 := hx.1 0
  simp only [path, affinePath, fieldCenter, fieldScale, Pi.sub_apply] at h0
  have h3 : -(m.width (2 * t - 1 / 2) i 0) ≤
      m.width (2 * t - 1 / 2) i 0 / A.width i 0 * (x 0 - A.center i 0) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hA]
    have : m.width (2 * t - 1 / 2) i 0 * (-(A.width i 0)) ≤
        m.width (2 * t - 1 / 2) i 0 * (x 0 - A.center i 0) :=
      mul_le_mul_of_nonneg_left (by linarith) hW.le
    linarith
  linarith

