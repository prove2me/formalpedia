-- Prove2me | solution 2 for OAI.BalancedTransport.FiniteMachine.Represents.advance
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T06:39:25.195541+00:00
-- url     : https://prove2.me/submissions/fb780734-1fe5-475b-b680-8675967d81aa

-- Generated from openai/math@1581d4c lean/OAI/MathematicalPhysics/NavierStokes/BalancedTransport/MachineHalting.lean:L94-L186
-- (upload_full_project.md Phase 4): solution for node OAI.BalancedTransport.FiniteMachine.Represents.advance. The node keeps its source
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

theorem advance (h : Represents M w c)
    (v : Transition (Fin (M.states + 1)) (Fin (M.symbols + 1)))
    (hv : M.normalized.transition w.state w.current = ⟨some v.state, v.write, v.move⟩) :
    Represents M (w.next M.normalized) (c.advance v) := by
  cases hm : v.move with
  | stay =>
      simp only [Checkpoint.next, hv, hm]
      constructor
      · simp [TapeConfiguration.advance, hm]
      · intro n
        change w.left n = Function.update c.tape c.head v.write
          (c.head + (match v.move with | .stay => 0 | .left => -1 | .right => 1) -
            ((n : ℤ) + 1))
        simp only [hm, add_zero]
        rw [Function.update_of_ne (by omega) _ _]
        exact h.left n
      · intro n
        simp only [TapeConfiguration.advance, hm, add_zero]
        rw [Function.update_of_ne (by omega) _ _]
        exact h.right n
  | left =>
      simp only [Checkpoint.next, hv, hm]
      constructor
      · simp only [TapeConfiguration.advance, hm, Stream'.head, Stream'.get]
        rw [Function.update_of_ne (by omega) _ _]
        simpa [sub_eq_add_neg] using h.left 0
      · intro n
        simp only [TapeConfiguration.advance, hm, Stream'.tail, Stream'.get]
        rw [Function.update_of_ne (by omega) _ _]
        convert h.left (n + 1) using 1
        congr 1
        omega
      · intro n
        simp only [TapeConfiguration.advance, hm]
        cases n with
        | zero => simp
        | succ n =>
            rw [Function.update_of_ne (by omega) _ _]
            simp only [List.getElem?_cons_succ]
            convert h.right n using 1
            congr 1
            omega
  | right =>
      cases hr : w.right with
      | nil =>
          simp only [Checkpoint.next, hv, hm, hr]
          constructor
          · simp only [TapeConfiguration.advance, hm]
            rw [Function.update_of_ne (by omega) _ _]
            change M.blank = c.tape (c.head + 1)
            simpa only [hr, List.getElem?_nil, Option.getD_none, Nat.cast_zero, zero_add]
              using h.right 0
          · intro n
            simp only [TapeConfiguration.advance, hm]
            cases n with
            | zero => simp [Stream'.cons]
            | succ n =>
                rw [Function.update_of_ne (by omega) _ _]
                simp only [Stream'.cons]
                convert h.left n using 1
                congr 1
                omega
          · intro n
            simp only [TapeConfiguration.advance, hm]
            rw [Function.update_of_ne (by omega) _ _]
            have he : c.head + 1 + ((n : ℤ) + 1) =
                c.head + (((n + 1 : ℕ) : ℤ) + 1) := by omega
            rw [he]
            simpa only [hr, List.getElem?_nil, Option.getD_none] using h.right (n + 1)
      | cons a r =>
          simp only [Checkpoint.next, hv, hm, hr]
          constructor
          · simp only [TapeConfiguration.advance, hm]
            rw [Function.update_of_ne (by omega) _ _]
            simpa only [hr, List.getElem?_cons_zero, Option.getD_some, Nat.cast_zero, zero_add]
              using h.right 0
          · intro n
            simp only [TapeConfiguration.advance, hm]
            cases n with
            | zero => simp [Stream'.cons]
            | succ n =>
                rw [Function.update_of_ne (by omega) _ _]
                simp only [Stream'.cons]
                convert h.left n using 1
                congr 1
                omega
          · intro n
            simp only [TapeConfiguration.advance, hm]
            rw [Function.update_of_ne (by omega) _ _]
            have he : c.head + 1 + ((n : ℤ) + 1) =
                c.head + (((n + 1 : ℕ) : ℤ) + 1) := by omega
            rw [he]
            simpa only [hr, List.getElem?_cons_succ] using h.right (n + 1)

end BalancedTransport.FiniteMachine.Represents
end

noncomputable section
namespace BalancedTransport.Recorder.Checkpoint

end BalancedTransport.Recorder.Checkpoint
end

noncomputable section
namespace BalancedTransport.FiniteMachine
open Recorder
variable {M : FiniteMachine}

end BalancedTransport.FiniteMachine
end

end OAI

-- ---- platform node ----
open OAI OAI.BalancedTransport OAI.BalancedTransport.FiniteMachine OAI.BalancedTransport.FiniteMachine.Represents
open Recorder
open Stream'


theorem solution : type_of% @_root_.OAI.BalancedTransport.FiniteMachine.Represents.advance := @_root_.OAI.BalancedTransport.FiniteMachine.Represents.advance
