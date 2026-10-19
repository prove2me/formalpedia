-- Prove2me | solution 1 for OAI.BalancedTransport.FiniteMachine.lift_step
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T06:02:20.264848+00:00
-- url     : https://prove2.me/submissions/cefa0680-beb9-411c-8696-a21d3ffd7a95

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

open OAI OAI.BalancedTransport OAI.BalancedTransport.FiniteMachine
open Recorder
variable {M : FiniteMachine}
theorem h45_adv {M : FiniteMachine} {w : M.WorkConfiguration} {c : TapeConfiguration M}
    (h : Represents M w c)
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

theorem h45_next_state {M : FiniteMachine} (w : M.WorkConfiguration) :
    (w.next M.normalized).state = (M.normalized.transition w.state w.current).state := by
  obtain ⟨st, L, cur, R, H⟩ := w
  unfold Checkpoint.next
  dsimp only
  rcases M.normalized.transition st cur with ⟨s, wr, mv⟩
  cases mv <;> cases R <;> rfl

theorem solution {c d : TapeConfiguration M} {w : M.WorkConfiguration}
    (h : machineStep M c = some d) (hs : w.state = some c.state)
    (ht : Represents M w c) :
    Checkpoint.WorkStep M.normalized w (w.next M.normalized) ∧
    (w.next M.normalized).state = some d.state ∧
    Represents M (w.next M.normalized) d := by
  have hex : ∃ v, M.transition c.state (c.tape c.head) = some v ∧ c.advance v = d := by
    unfold machineStep at h
    rcases hm : M.transition c.state (c.tape c.head) with _ | v
    · rw [hm] at h; simp at h
    · rw [hm] at h
      simp at h
      exact ⟨v, rfl, h⟩
  obtain ⟨v, hv0, rfl⟩ := hex
  have hv : M.normalized.transition w.state w.current = ⟨some v.state, v.write, v.move⟩ := by
    rw [hs, ht.current]; simp [normalized, hv0]
  refine ⟨⟨by rw [hs]; simp [normalized], rfl⟩, ?_, h45_adv ht v hv⟩
  rw [h45_next_state, hv]
  rfl

