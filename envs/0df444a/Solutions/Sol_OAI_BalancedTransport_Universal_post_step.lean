-- Prove2me | solution 1 for OAI.BalancedTransport.Universal.post_step
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T05:25:27.51268+00:00
-- url     : https://prove2.me/submissions/a0f88b68-3331-421b-88c0-f5ece096a712

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

open OAI OAI.BalancedTransport OAI.BalancedTransport.Universal
open Turing StateTransition
open scoped Classical
variable {Γ Λ : Type*} [Fintype Γ] [Inhabited Γ] [Inhabited Λ]
variable (P : TM0.Machine Γ Λ) (S : Finset Λ) (ss : TM0.Supports P S)


theorem solution (c : TM0.Cfg Γ Λ) (d : TapeConfiguration (finitePostMachine P S ss))
    (h : PostRel P S ss c d) :
    match TM0.step P c with
    | none => machineStep (finitePostMachine P S ss) d = none
    | some c' => ∃ d', machineStep (finitePostMachine P S ss) d = some d' ∧ PostRel P S ss c' d' := by
  rcases c with ⟨q, T⟩
  obtain ⟨hq, hst, htape⟩ := h
  simp only at hq hst htape
  have h0 : d.tape d.head = finiteIndex T.head := by simpa using htape 0
  have hidx : (finiteUnindex (⟨default, ss.1⟩ : {q : Λ // q ∈ S}) d.state).val = q := by
    rw [hst]; simp [stateIndex, hq]
  have hsym : finiteUnindex (default : Γ) (d.tape d.head) = T.head := by rw [h0]; simp
  have htr : (finitePostMachine P S ss).transition d.state (d.tape d.head) =
      (P q T.head).map (postInstruction P S ss (d.tape d.head)) := by
    show (P (finiteUnindex ⟨default, ss.1⟩ d.state : {q : Λ // q ∈ S}).val
      (finiteUnindex default (d.tape d.head))).map _ = _
    rw [hidx, hsym]
  simp only [TM0.step]
  unfold machineStep
  rw [htr]
  rcases hP : P q T.head with _ | ⟨q', s⟩
  · simp
  · simp only [Option.map_some]
    refine ⟨_, rfl, ?_⟩
    refine ⟨ss.2 (by rw [hP]; rfl) hq, rfl, ?_⟩
    intro i
    cases s with
    | move dir =>
      cases dir with
      | left =>
        simp only [postInstruction]
        rw [Function.update_apply, Tape.move_left_nth]
        split_ifs with he
        · have : i = 1 := by omega
          subst this
          rw [h0]; simp
        · rw [show d.head + -1 + i = d.head + (i - 1) by ring, htape]
      | right =>
        simp only [postInstruction]
        rw [Function.update_apply, Tape.move_right_nth]
        split_ifs with he
        · have : i = -1 := by omega
          subst this
          rw [h0]; simp
        · rw [show d.head + 1 + i = d.head + (i + 1) by ring, htape]
    | write b =>
      simp only [postInstruction]
      rw [Function.update_apply, Tape.write_nth]
      split_ifs with he he2 he2
      · rfl
      · omega
      · omega
      · rw [show d.head + 0 + i = d.head + i by ring, htape]

