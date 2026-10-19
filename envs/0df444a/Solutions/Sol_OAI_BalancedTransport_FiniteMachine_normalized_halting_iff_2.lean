-- Prove2me | solution 2 for OAI.BalancedTransport.FiniteMachine.normalized_halting_iff
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T06:43:35.646986+00:00
-- url     : https://prove2.me/submissions/b3c0b9b8-e1e7-4eac-a1b5-d52a33a2da4d

-- Generated from openai/math@1581d4c lean/OAI/MathematicalPhysics/NavierStokes/BalancedTransport/MachineHalting.lean:L300-L316
-- (upload_full_project.md Phase 4): solution for node OAI.BalancedTransport.FiniteMachine.normalized_halting_iff. The node keeps its source
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
import Theorems.Thm_OAI_BalancedTransport_FiniteMachine_lift_step

-- ---- from OAI.MathematicalPhysics.NavierStokes.BalancedTransport.MachineHalting ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

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

theorem initialWork_represents (M : FiniteMachine) (w : Input M) :
    Represents M (M.initialWork w) (initialConfiguration M w) := by
  constructor
  · cases w <;> simp [initialWork, Checkpoint.initial, normalized, initialConfiguration]
  · intro n
    change M.blank = (if 0 ≤ (0 : ℤ) - ((n : ℤ) + 1)
      then w[((0 : ℤ) - ((n : ℤ) + 1)).toNat]?.getD M.blank else M.blank)
    rw [ite_eq_right (by omega)]
  · intro n
    simp only [initialWork, Checkpoint.initial, normalized, initialConfiguration, zero_add,
      show (0 : ℤ) ≤ (n : ℤ) + 1 by omega, ↓reduceIte]
    have hn : ((n : ℤ) + 1).toNat = n + 1 := by omega
    rw [hn]
    cases w <;> simp

end BalancedTransport.FiniteMachine
end

noncomputable section
namespace BalancedTransport.FiniteMachine.Represents
open Recorder
open Stream'
variable {M : FiniteMachine} {w : M.WorkConfiguration} {c : TapeConfiguration M}

theorem stop (h : Represents M w c)
    (hv : M.normalized.transition w.state w.current = ⟨none, w.current, .stay⟩) :
    Represents M (w.next M.normalized) c := by
  simp only [Checkpoint.next, hv]
  exact ⟨h.current, h.left, h.right⟩

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

theorem lift_execution {c d : TapeConfiguration M}
    (h : Relation.ReflTransGen (fun c d => machineStep M c = some d) c d)
    {w : M.WorkConfiguration} (hs : w.state = some c.state) (ht : Represents M w c) :
    ∃ w', Relation.ReflTransGen (Checkpoint.WorkStep M.normalized) w w' ∧
      w'.state = some d.state ∧ Represents M w' d := by
  induction h with
  | refl => exact ⟨w, .refl, hs, ht⟩
  | @tail c' d hc' hd ih =>
      obtain ⟨w', hw', hs', ht'⟩ := ih
      obtain ⟨hstep, hs'', ht''⟩ := lift_step hd hs' ht'
      exact ⟨w'.next M.normalized, hw'.tail hstep, hs'', ht''⟩

theorem lift_halt {c : TapeConfiguration M} {w : M.WorkConfiguration}
    (h : machineStep M c = none) (hs : w.state = some c.state)
    (ht : Represents M w c) :
    Checkpoint.WorkStep M.normalized w (w.next M.normalized) ∧
    (w.next M.normalized).state = none := by
  have hv : M.transition c.state (c.tape c.head) = none := by
    simpa only [machineStep, Option.map_eq_none_iff] using h
  have hv' : M.normalized.transition w.state w.current =
      ⟨none, w.current, .stay⟩ := by
    simp [normalized, hs, ht.current, hv]
  refine ⟨⟨?_, rfl⟩, ?_⟩
  · simp [normalized, hs]
  · rw [Checkpoint.next_state, hv']

theorem reflect_step {c : TapeConfiguration M} {w w' : M.WorkConfiguration}
    (hc : Corresponds M w c) (h : Checkpoint.WorkStep M.normalized w w') :
    ∃ d, Relation.ReflTransGen (fun c d => machineStep M c = some d) c d ∧
      Corresponds M w' d := by
  obtain ⟨ht, hs | ⟨hs, _⟩⟩ := hc
  · obtain ⟨hnh, rfl⟩ := h
    cases hv : M.transition c.state (c.tape c.head) with
    | none =>
        have hv' : M.normalized.transition w.state w.current =
            ⟨none, w.current, .stay⟩ := by
          simp [normalized, hs, ht.current, hv]
        refine ⟨c, .refl, ht.stop hv', Or.inr ⟨?_, ?_⟩⟩
        · rw [Checkpoint.next_state, hv']
        · simp [machineStep, hv]
    | some v =>
        have hd : machineStep M c = some (c.advance v) := by
          cases hm : v.move <;> simp [machineStep, hv, TapeConfiguration.advance, hm]
        obtain ⟨_, hs', ht'⟩ := lift_step hd hs ht
        exact ⟨c.advance v, .single hd, ht', Or.inl hs'⟩
  · exact False.elim (h.1 hs)

theorem reflect_execution {c : TapeConfiguration M} {w w' : M.WorkConfiguration}
    (hc : Corresponds M w c)
    (h : Relation.ReflTransGen (Checkpoint.WorkStep M.normalized) w w') :
    ∃ d, Relation.ReflTransGen (fun c d => machineStep M c = some d) c d ∧
      Corresponds M w' d := by
  induction h with
  | refl => exact ⟨c, .refl, hc⟩
  | @tail w' w'' hw' hstep ih =>
      obtain ⟨d, hd, hcd⟩ := ih
      obtain ⟨e, he, hce⟩ := reflect_step hcd hstep
      exact ⟨e, hd.trans he, hce⟩

theorem normalized_halting_iff (M : FiniteMachine) (input : Input M) :
    (∃ w', Relation.ReflTransGen (Checkpoint.WorkStep M.normalized)
      (M.initialWork input) w' ∧ w'.state = M.normalized.halt) ↔ Halts M input := by
  constructor
  · rintro ⟨w', hw', hhalt⟩
    have hc : Corresponds M (M.initialWork input) (initialConfiguration M input) :=
      ⟨initialWork_represents M input, Or.inl rfl⟩
    obtain ⟨d, hd, _, hs | ⟨_, hterm⟩⟩ := reflect_execution hc hw'
    · simp only [normalized] at hhalt
      rw [hhalt] at hs
      cases hs
    · exact ⟨d, hd, hterm⟩
  · rintro ⟨d, hd, hterm⟩
    obtain ⟨w', hw', hs', ht'⟩ := lift_execution hd (w := M.initialWork input)
      rfl (initialWork_represents M input)
    obtain ⟨hst, hh⟩ := lift_halt hterm hs' ht'
    exact ⟨w'.next M.normalized, hw'.tail hst, hh⟩

end BalancedTransport.FiniteMachine
end

end OAI

-- ---- platform node ----
open OAI OAI.BalancedTransport OAI.BalancedTransport.FiniteMachine
open Recorder


theorem solution : type_of% @_root_.OAI.BalancedTransport.FiniteMachine.normalized_halting_iff := @_root_.OAI.BalancedTransport.FiniteMachine.normalized_halting_iff
