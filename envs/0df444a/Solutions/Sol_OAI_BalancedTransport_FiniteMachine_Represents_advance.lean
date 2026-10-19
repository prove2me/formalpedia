-- Prove2me | solution 1 for OAI.BalancedTransport.FiniteMachine.Represents.advance
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T06:01:45.875304+00:00
-- url     : https://prove2.me/submissions/a607b5db-cb12-4c2f-a540-71c4599dc78c

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

open OAI OAI.BalancedTransport OAI.BalancedTransport.FiniteMachine OAI.BalancedTransport.FiniteMachine.Represents
open Recorder
open Stream'
variable {M : FiniteMachine} {w : M.WorkConfiguration} {c : TapeConfiguration M}


theorem solution (h : Represents M w c)
    (v : Transition (Fin (M.states + 1)) (Fin (M.symbols + 1)))
    (hv : M.normalized.transition w.state w.current = ⟨some v.state, v.write, v.move⟩) :
    Represents M (w.next M.normalized) (c.advance v) := by
  obtain ⟨hc, hl, hr⟩ := h
  obtain ⟨st, L, cur, R, H⟩ := w
  obtain ⟨q, a, mv⟩ := v
  simp only at hc hl hr hv
  cases mv with
  | stay =>
    have hn : Checkpoint.next M.normalized ⟨st, L, cur, R, H⟩ =
        ⟨some q, L, a, R, Stream'.cons (Letter.record (.stay st cur)) H⟩ := by
      simp [Checkpoint.next, hv]
    rw [hn]
    refine ⟨?_, ?_, ?_⟩
    · simp [TapeConfiguration.advance]
    · intro n
      simp only [TapeConfiguration.advance, add_zero]
      rw [Function.update_of_ne (by omega), hl n]
    · intro n
      simp only [TapeConfiguration.advance, add_zero]
      rw [Function.update_of_ne (by omega), hr n]
  | left =>
    have hn : Checkpoint.next M.normalized ⟨st, L, cur, R, H⟩ =
        ⟨some q, L.tail, L.head, a :: R, Stream'.cons (Letter.record (.left st cur L.head)) H⟩ := by
      simp [Checkpoint.next, hv]
    rw [hn]
    refine ⟨?_, ?_, ?_⟩
    · simp only [TapeConfiguration.advance]
      rw [Function.update_of_ne (by omega)]
      show L 0 = _
      rw [hl 0]; all_goals (congr 1 <;> omega)
    · intro n
      simp only [TapeConfiguration.advance]
      rw [Function.update_of_ne (by omega)]
      show L (n + 1) = _
      rw [hl (n + 1)]; all_goals (congr 1 <;> omega)
    · intro n
      simp only [TapeConfiguration.advance]
      cases n with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.getD_some]
        rw [show c.head + -1 + (((0:ℕ):ℤ) + 1) = c.head by omega]
        simp
      | succ n =>
        simp only [List.getElem?_cons_succ]
        rw [Function.update_of_ne (by omega), hr n]; all_goals (congr 1 <;> omega)
  | right =>
    cases R with
    | nil =>
      have hn : Checkpoint.next M.normalized ⟨st, L, cur, [], H⟩ =
          ⟨some q, Stream'.cons a L, M.blank, [], Stream'.cons (Letter.record (.extend st cur)) H⟩ := by
        simp only [Checkpoint.next, hv]
        try rfl
      rw [hn]
      refine ⟨?_, ?_, ?_⟩
      · simp only [TapeConfiguration.advance]
        rw [Function.update_of_ne (by omega)]
        have := hr 0
        simp at this
        rw [this]
      · intro n
        simp only [TapeConfiguration.advance]
        cases n with
        | zero =>
          rw [show c.head + 1 - (((0:ℕ):ℤ) + 1) = c.head by omega]
          rw [Function.update_self]; rfl
        | succ n =>
          rw [Function.update_of_ne (by omega)]
          show L n = _
          rw [hl n]; all_goals (congr 1 <;> omega)
      · intro n
        simp only [TapeConfiguration.advance]
        rw [Function.update_of_ne (by omega)]
        have := hr (n + 1)
        simp only [List.getElem?_nil, Option.getD_none] at this ⊢
        rw [this]; all_goals (congr 1 <;> omega)
    | cons b R' =>
      have hn : Checkpoint.next M.normalized ⟨st, L, cur, b :: R', H⟩ =
          ⟨some q, Stream'.cons a L, b, R', Stream'.cons (Letter.record (.right st cur b)) H⟩ := by
        simp [Checkpoint.next, hv]
      rw [hn]
      refine ⟨?_, ?_, ?_⟩
      · simp only [TapeConfiguration.advance]
        rw [Function.update_of_ne (by omega)]
        have := hr 0
        simp at this
        rw [this]
      · intro n
        simp only [TapeConfiguration.advance]
        cases n with
        | zero =>
          rw [show c.head + 1 - (((0:ℕ):ℤ) + 1) = c.head by omega]
          rw [Function.update_self]; rfl
        | succ n =>
          rw [Function.update_of_ne (by omega)]
          show L n = _
          rw [hl n]; all_goals (congr 1 <;> omega)
      · intro n
        simp only [TapeConfiguration.advance]
        rw [Function.update_of_ne (by omega)]
        have := hr (n + 1)
        simp only [List.getElem?_cons_succ] at this
        rw [this]; all_goals (congr 1 <;> omega)

