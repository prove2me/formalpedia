-- Prove2me | solution 2 for OAI.BalancedTransport.Geometry.BoxLayout.separated_of_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T06:53:08.318388+00:00
-- url     : https://prove2.me/submissions/3e012ab3-f136-4fdf-bc4b-e0ec3a1c2287

-- Generated from openai/math@1581d4c lean/OAI/MathematicalPhysics/NavierStokes/BalancedTransport/CompiledGeometry.lean:L19-L43
-- (upload_full_project.md Phase 4): solution for node OAI.BalancedTransport.Geometry.BoxLayout.separated_of_disjoint. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
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
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_CompiledGeometry

-- ---- from OAI.MathematicalPhysics.NavierStokes.BalancedTransport.MotionField ----
namespace OAI

noncomputable section
namespace BalancedTransport.Geometry.BoxLayout
open Set Filter
open scoped Topology
variable {ι : Type*} [Fintype ι]

omit [Fintype ι] in
lemma mem_solid {A : BoxLayout ι} {i : ι} {x : Space} : x ∈ A.solid i ↔
    ∀ k, A.center i k - A.width i k ≤ x k ∧ x k ≤ A.center i k + A.width i k := by
  simp only [solid, mem_Icc, Pi.le_def, Pi.sub_apply, Pi.add_apply]
  exact forall_and.symm

end BalancedTransport.Geometry.BoxLayout
end

noncomputable section
namespace BalancedTransport.Geometry.BoxMotion
open Set Filter
open scoped Topology
variable {ι : Type*} [Fintype ι]
variable {A B : BoxLayout ι} {safe : Set ι} {η : ℝ}

end BalancedTransport.Geometry.BoxMotion
end

end OAI

-- ---- from OAI.MathematicalPhysics.NavierStokes.BalancedTransport.CompiledGeometry ----
namespace OAI

noncomputable section
namespace BalancedTransport.Geometry
open Set
variable {ι : Type*} [Fintype ι]

omit [Fintype ι] in
lemma BoxLayout.separated_of_disjoint {A : BoxLayout ι} (hp : A.Positive)
    (hs : Pairwise fun i j => Disjoint (A.solid i) (A.solid j)) : A.Separated 0 := by
  intro i j hij
  by_contra! h
  let x : Space := fun k => max (A.center i k - A.width i k) (A.center j k - A.width j k)
  have hh (k : Fin 3) :
      -(A.width i k + A.width j k) ≤ A.center i k - A.center j k ∧
      A.center i k - A.center j k ≤ A.width i k + A.width j k := by
    have := h k
    simp only [mul_zero, add_zero] at this
    exact abs_le.mp this
  have hi : x ∈ A.solid i := by
    rw [BoxLayout.mem_solid]
    intro k
    refine ⟨le_max_left _ _, max_le ?_ ?_⟩
    · linarith [hp i k]
    · linarith [(hh k).1]
  have hj : x ∈ A.solid j := by
    rw [BoxLayout.mem_solid]
    intro k
    refine ⟨le_max_right _ _, max_le ?_ ?_⟩
    · linarith [(hh k).2]
    · linarith [hp j k]
  exact Set.disjoint_left.mp (hs hij) hi hj

end BalancedTransport.Geometry
end

noncomputable section
namespace BalancedTransport.Coding
open BalancedTransport.Geometry
variable {S ι : Type*}

end BalancedTransport.Coding
end

noncomputable section
namespace BalancedTransport.Recorder
open BalancedTransport.Geometry
variable {Q Γ : Type*} [Fintype Q] [Fintype Γ] [DecidableEq Q] [DecidableEq Γ]

end BalancedTransport.Recorder
end

end OAI

-- ---- platform node ----
open OAI OAI.BalancedTransport OAI.BalancedTransport.Geometry
open Set


theorem solution : type_of% @_root_.OAI.BalancedTransport.Geometry.BoxLayout.separated_of_disjoint := @_root_.OAI.BalancedTransport.Geometry.BoxLayout.separated_of_disjoint
