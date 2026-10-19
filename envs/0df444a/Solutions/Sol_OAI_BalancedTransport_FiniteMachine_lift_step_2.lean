-- Prove2me | solution 2 for OAI.BalancedTransport.FiniteMachine.lift_step
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T06:41:30.054998+00:00
-- url     : https://prove2.me/submissions/57b96a22-37a1-4f9d-adf7-6404e37887cd

-- Generated from openai/math@1581d4c lean/OAI/MathematicalPhysics/NavierStokes/BalancedTransport/MachineHalting.lean:L214-L234
-- (upload_full_project.md Phase 4): solution for node OAI.BalancedTransport.FiniteMachine.lift_step. The node keeps its source
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
import Theorems.Thm_OAI_BalancedTransport_FiniteMachine_Represents_advance

-- ---- from OAI.MathematicalPhysics.NavierStokes.BalancedTransport.MachineHalting ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section
namespace BalancedTransport.Recorder.Checkpoint

end BalancedTransport.Recorder.Checkpoint
end

noncomputable section
namespace BalancedTransport.FiniteMachine

end BalancedTransport.FiniteMachine
end

noncomputable section
namespace BalancedTransport.TapeConfiguration

end BalancedTransport.TapeConfiguration
end

noncomputable section
namespace BalancedTransport.FiniteMachine
open Recorder
open Stream'

end BalancedTransport.FiniteMachine
end

noncomputable section
namespace BalancedTransport.FiniteMachine.Represents
open Recorder
open Stream'
variable {M : FiniteMachine} {w : M.WorkConfiguration} {c : TapeConfiguration M}

end BalancedTransport.FiniteMachine.Represents
end

noncomputable section
namespace BalancedTransport.Recorder.Checkpoint

theorem next_state {Q Γ : Type*} (M : Machine Q Γ) (w : Checkpoint Q Γ) :
    (w.next M).state = (M.transition w.state w.current).state := by
  cases hm : (M.transition w.state w.current).move <;>
    simp only [next, hm]
  cases w.right <;> rfl

end BalancedTransport.Recorder.Checkpoint
end

noncomputable section
namespace BalancedTransport.FiniteMachine
open Recorder
variable {M : FiniteMachine}

theorem lift_step {c d : TapeConfiguration M} {w : M.WorkConfiguration}
    (h : machineStep M c = some d) (hs : w.state = some c.state)
    (ht : Represents M w c) :
    Checkpoint.WorkStep M.normalized w (w.next M.normalized) ∧
    (w.next M.normalized).state = some d.state ∧
    Represents M (w.next M.normalized) d := by
  cases hv : M.transition c.state (c.tape c.head) with
  | none => simp [machineStep, hv] at h
  | some v =>
      have hd : c.advance v = d := by
        cases hm : v.move <;>
          simpa only [machineStep, hv, Option.map_some, Option.some.injEq,
            TapeConfiguration.advance, hm] using h
      subst d
      have hv' : M.normalized.transition w.state w.current =
          ⟨some v.state, v.write, v.move⟩ := by
        simp [normalized, hs, ht.current, hv]
      refine ⟨⟨?_, rfl⟩, ?_, ht.advance v hv'⟩
      · simp [normalized, hs]
      · rw [Checkpoint.next_state, hv']
        rfl

end BalancedTransport.FiniteMachine
end

end OAI

-- ---- platform node ----
open OAI OAI.BalancedTransport OAI.BalancedTransport.FiniteMachine
open Recorder


theorem solution : type_of% @_root_.OAI.BalancedTransport.FiniteMachine.lift_step := @_root_.OAI.BalancedTransport.FiniteMachine.lift_step
