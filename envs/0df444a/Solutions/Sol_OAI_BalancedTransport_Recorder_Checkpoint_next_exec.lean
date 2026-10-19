-- Prove2me | solution 1 for OAI.BalancedTransport.Recorder.Checkpoint.next_exec
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T05:59:17.834051+00:00
-- url     : https://prove2.me/submissions/42efc2dd-3cb2-4ab8-9740-8936d46bcb39

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

open OAI OAI.BalancedTransport OAI.BalancedTransport.Recorder OAI.BalancedTransport.Recorder.Checkpoint
variable {Q Γ : Type*}
open Stream' Letter Control
theorem h45_trans {Q Γ : Type*} {M : Machine Q Γ} {n m : ℕ} {c d e : Configuration Q Γ}
    (h1 : Exec M n c d) (h2 : Exec M m d e) : Exec M (n + m) c e := by
  induction h1 with
  | refl c => simpa using h2
  | cons hs _ ih =>
    rw [Nat.add_right_comm]
    exact Exec.cons hs (ih h2)

theorem h45_out {Q Γ : Type*} (M : Machine Q Γ) (q : Q) (hq : q ≠ M.halt) (s : List Γ)
    (L T H : Stream' (Letter Q Γ)) :
    Exec M s.length ⟨Control.outward q, L, s.map Letter.work ++ₛ T, H⟩
      ⟨Control.outward q, (s.map Letter.work).reverse ++ₛ L, T, H⟩ := by
  induction s generalizing L with
  | nil =>
    simp only [List.map_nil, List.reverse_nil, List.length_nil, Stream'.nil_append_stream]
    exact Exec.refl _
  | cons a s ih =>
    have hs : Step M ⟨Control.outward q, L, (a :: s).map Letter.work ++ₛ T, H⟩
        ⟨Control.outward q, Letter.work a :: L, s.map Letter.work ++ₛ T, H⟩ :=
      ⟨.outward q a, hq, ⟨L, s.map Letter.work ++ₛ T, H⟩,
        by simp [Row.instruction, Instruction.source, Stream'.cons_append_stream],
        by simp [Row.instruction, Instruction.target, Stream'.cons_append_stream]⟩
    have h := Exec.cons hs (ih (Letter.work a :: L))
    simpa [Stream'.append_append_stream, Stream'.cons_append_stream] using h

theorem h45_back {Q Γ : Type*} (M : Machine Q Γ) (q : Q) (hq : q ≠ M.halt) (s : List Γ)
    (L T H : Stream' (Letter Q Γ)) :
    Exec M s.length ⟨Control.returning q, s.map Letter.work ++ₛ L, T, H⟩
      ⟨Control.returning q, L, (s.map Letter.work).reverse ++ₛ T, H⟩ := by
  induction s generalizing T with
  | nil =>
    simp only [List.map_nil, List.reverse_nil, List.length_nil, Stream'.nil_append_stream]
    exact Exec.refl _
  | cons a s ih =>
    have hs : Step M ⟨Control.returning q, (a :: s).map Letter.work ++ₛ L, T, H⟩
        ⟨Control.returning q, s.map Letter.work ++ₛ L, Letter.work a :: T, H⟩ :=
      ⟨.backward q a, hq, ⟨s.map Letter.work ++ₛ L, T, H⟩,
        by simp [Row.instruction, Instruction.source, Stream'.cons_append_stream],
        by simp [Row.instruction, Instruction.target, Stream'.cons_append_stream]⟩
    have h := Exec.cons hs (ih (Letter.work a :: T))
    simpa [Stream'.append_append_stream, Stream'.cons_append_stream] using h

theorem solution (M : Machine Q Γ) (c : Checkpoint Q Γ) (hc : c.state ≠ M.halt) :
    Exec M (2 * (c.right.length + 1) + 2) (c.expand M) ((c.next M).expand M) := by
  obtain ⟨q, cl, cur, cr, ch⟩ := c
  simp only at hc
  have hconst : Stream'.const (work M.blank : Letter Q Γ) =
      work M.blank :: Stream'.const (work M.blank) := Stream'.const_eq _
  have s1 : Step M (Checkpoint.expand M ⟨q, cl, cur, cr, ch⟩)
      ⟨Control.outward q, marked cur :: Stream'.map work cl,
        cr.map work ++ₛ (boundary :: Stream'.const (work M.blank)), ch⟩ :=
    ⟨.enter q cur, hc, ⟨Stream'.map work cl, cr.map work ++ₛ (boundary :: Stream'.const (work M.blank)), ch⟩,
      by simp [Row.instruction, Instruction.source, Checkpoint.expand, Stream'.cons_append_stream],
      by simp [Row.instruction, Instruction.target, Stream'.cons_append_stream]⟩
  have e2 := h45_out M q hc cr (marked cur :: Stream'.map work cl)
    (boundary :: Stream'.const (work M.blank)) ch
  have s3 : Step M ⟨Control.outward q, (cr.map work).reverse ++ₛ (marked cur :: Stream'.map work cl),
        boundary :: Stream'.const (work M.blank), ch⟩
      ⟨Control.returning q, (cr.map work).reverse ++ₛ (marked cur :: Stream'.map work cl),
        boundary :: Stream'.const (work M.blank), work M.blank :: ch⟩ :=
    ⟨.supply q, hc, ⟨(cr.map work).reverse ++ₛ (marked cur :: Stream'.map work cl),
        Stream'.const (work M.blank), ch⟩,
      by
        simp only [Row.instruction, Instruction.source, Stream'.cons_append_stream,
          Stream'.nil_append_stream]
        rw [← hconst],
      by simp [Row.instruction, Instruction.target, Stream'.cons_append_stream]⟩
  have e4 := h45_back M q hc cr.reverse (marked cur :: Stream'.map work cl)
    (boundary :: Stream'.const (work M.blank)) (work M.blank :: ch)
  simp only [List.map_reverse, List.reverse_reverse, List.length_reverse] at e4
  have s5 : Step M ⟨Control.returning q, marked cur :: Stream'.map work cl,
        cr.map work ++ₛ (boundary :: Stream'.const (work M.blank)), work M.blank :: ch⟩
      ⟨Control.execute q, Stream'.map work cl,
        work cur :: (cr.map work ++ₛ (boundary :: Stream'.const (work M.blank))), work M.blank :: ch⟩ :=
    ⟨.restore q cur, hc, ⟨Stream'.map work cl,
        cr.map work ++ₛ (boundary :: Stream'.const (work M.blank)), work M.blank :: ch⟩,
      by simp [Row.instruction, Instruction.source, Stream'.cons_append_stream],
      by simp [Row.instruction, Instruction.target, Stream'.cons_append_stream]⟩
  have hcl : Stream'.map (work : Γ → Letter Q Γ) cl =
      (work cl.head : Letter Q Γ) :: Stream'.map (work : Γ → Letter Q Γ) cl.tail := by
    rw [← Stream'.map_cons, Stream'.eta]
  have s6 : Step M ⟨Control.execute q, Stream'.map work cl,
        work cur :: (cr.map work ++ₛ (boundary :: Stream'.const (work M.blank))), work M.blank :: ch⟩
      ((Checkpoint.next M ⟨q, cl, cur, cr, ch⟩).expand M) := by
    rcases hm : (M.transition q cur).move with _ | _ | _
    · refine ⟨.stay q cur, ⟨hc, hm⟩, ⟨Stream'.map work cl,
        cr.map work ++ₛ (boundary :: Stream'.const (work M.blank)), ch⟩, ?_, ?_⟩
      · simp [Row.instruction, Instruction.source, Stream'.cons_append_stream]
      · simp [Row.instruction, Instruction.target, Checkpoint.next, Checkpoint.expand, hm,
          Stream'.cons_append_stream]
    · refine ⟨.left q cur cl.head, ⟨hc, hm⟩, ⟨Stream'.map work cl.tail,
        cr.map work ++ₛ (boundary :: Stream'.const (work M.blank)), ch⟩, ?_, ?_⟩
      · simp only [Row.instruction, Instruction.source, Stream'.cons_append_stream,
          Stream'.nil_append_stream]
        rw [hcl]
      · simp [Row.instruction, Instruction.target, Checkpoint.next, Checkpoint.expand, hm,
          Stream'.cons_append_stream]
    · cases cr with
      | nil =>
        refine ⟨.extend q cur, ⟨hc, hm⟩, ⟨Stream'.map work cl, Stream'.const (work M.blank), ch⟩, ?_, ?_⟩
        · simp only [Row.instruction, Instruction.source, Stream'.cons_append_stream,
            Stream'.nil_append_stream, List.map_nil]
          rw [← hconst]
        · simp [Row.instruction, Instruction.target, Checkpoint.next, Checkpoint.expand, hm,
            Stream'.cons_append_stream, Stream'.map_cons]
      | cons b cr' =>
        refine ⟨.right q cur b, ⟨hc, hm⟩, ⟨Stream'.map work cl,
          cr'.map work ++ₛ (boundary :: Stream'.const (work M.blank)), ch⟩, ?_, ?_⟩
        · simp [Row.instruction, Instruction.source, Stream'.cons_append_stream]
        · simp [Row.instruction, Instruction.target, Checkpoint.next, Checkpoint.expand, hm,
            Stream'.cons_append_stream, Stream'.map_cons]
  have total := Exec.cons s1 (h45_trans e2 (Exec.cons s3 (h45_trans e4
    (Exec.cons s5 (Exec.cons s6 (Exec.refl _))))))
  have hcast : ∀ {n m : ℕ} {a b : Configuration Q Γ}, n = m → Exec M n a b → Exec M m a b := by
    intro n m a b h e; subst h; exact e
  refine hcast ?_ total
  dsimp only
  omega

