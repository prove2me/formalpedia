-- Prove2me | solution 1 for OAI.SingleFold.Counter.eval_dom_iff_halts
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T18:11:51.984985+00:00
-- url     : https://prove2.me/submissions/a47c03b4-a7f4-4503-9866-15069c4f403d

import Mathlib
import Definitions.Def_SingleFold
import Definitions.Def_OAI_NumberTheory_SingleFold_PolynomialCompiler
import Definitions.Def_OAI_NumberTheory_SingleFold_RationalCodes
import Definitions.Def_OAI_NumberTheory_SingleFold_EllipticCoordinates
import Definitions.Def_OAI_NumberTheory_SingleFold_FunctionalCompiler
import Definitions.Def_OAI_NumberTheory_SingleFold_DescentMap
import Definitions.Def_OAI_NumberTheory_SingleFold_SquareSupport
import Definitions.Def_OAI_NumberTheory_SingleFold_LocalDescent
import Definitions.Def_OAI_NumberTheory_SingleFold_EllipticHeight
import Definitions.Def_OAI_NumberTheory_SingleFold_QuadraticHeight
import Definitions.Def_OAI_NumberTheory_SingleFold_FiniteGeneration
import Definitions.Def_OAI_NumberTheory_SingleFold_Rank
import Definitions.Def_OAI_NumberTheory_SingleFold_Duplication
import Definitions.Def_OAI_NumberTheory_SingleFold_Torsion
import Definitions.Def_OAI_NumberTheory_SingleFold_EllipticGrowth
import Definitions.Def_OAI_NumberTheory_SingleFold_Pell
import Definitions.Def_OAI_NumberTheory_SingleFold_Power
import Definitions.Def_OAI_NumberTheory_SingleFold_Binary
import Definitions.Def_OAI_NumberTheory_SingleFold_Packed
import Definitions.Def_OAI_NumberTheory_SingleFold_CounterMachine
import Definitions.Def_OAI_NumberTheory_SingleFold_CounterBounds
import Definitions.Def_OAI_NumberTheory_SingleFold_CounterCompilation
import Definitions.Def_OAI_NumberTheory_SingleFold_MacroMachine

open OAI OAI.SingleFold OAI.SingleFold.Counter
open StateTransition Relation
variable {Q J : Type} [DecidableEq Q] [DecidableEq J]
theorem h49_run_succ {Q J : Type} [DecidableEq Q] [DecidableEq J] (M : OAI.SingleFold.Counter.Machine Q J) (d : J → ℕ) (t : ℕ) :
    OAI.SingleFold.Counter.run M d (t+1) = OAI.SingleFold.Counter.next M (OAI.SingleFold.Counter.run M d t) := by
  unfold OAI.SingleFold.Counter.run
  rw [Function.iterate_succ_apply']

theorem h49_step_none {Q J : Type} [DecidableEq Q] [DecidableEq J] (M : OAI.SingleFold.Counter.Machine Q J) (c : OAI.SingleFold.Counter.Cfg Q J) :
    OAI.SingleFold.Counter.step M c = none ↔ c.state = M.halt := by
  rw [← M.halt_iff]
  unfold OAI.SingleFold.Counter.step
  cases M.instr c.state <;> simp

theorem h49_step_some {Q J : Type} [DecidableEq Q] [DecidableEq J] (M : OAI.SingleFold.Counter.Machine Q J) (c : OAI.SingleFold.Counter.Cfg Q J)
    (h : c.state ≠ M.halt) :
    OAI.SingleFold.Counter.step M c = some (OAI.SingleFold.Counter.next M c) := by
  rw [Ne, ← M.halt_iff] at h
  unfold OAI.SingleFold.Counter.step
  cases hi : M.instr c.state <;> simp_all

theorem solution (M : Machine Q J) (d : J → ℕ) :
    (eval (step M) ⟨M.start,d⟩).Dom ↔ Halts M d := by
  rw [Part.dom_iff_mem]
  simp only [StateTransition.mem_eval]
  constructor
  · rintro ⟨b, hr, hb⟩
    have : ∃ t, b = run M d t := by
      clear hb
      induction hr with
      | refl => exact ⟨0, rfl⟩
      | tail _ hbc ih =>
        obtain ⟨t, rfl⟩ := ih
        refine ⟨t+1, ?_⟩
        rw [h49_run_succ]
        by_cases hs : (run M d t).state = M.halt
        · rw [(h49_step_none M _).2 hs] at hbc; simp at hbc
        · rw [h49_step_some M _ hs] at hbc
          simp at hbc; exact hbc.symm
    obtain ⟨t, rfl⟩ := this
    rw [h49_step_none] at hb
    classical
    have hex : ∃ t, (run M d t).state = M.halt := ⟨t, hb⟩
    exact ⟨Nat.find hex, Nat.find_spec hex, fun s hs => Nat.find_min hex hs⟩
  · rintro ⟨T, hT, hlt⟩
    refine ⟨run M d T, ?_, (h49_step_none M _).2 hT⟩
    have : ∀ t ≤ T, Reaches (step M) ⟨M.start, d⟩ (run M d t) := by
      intro t
      induction t with
      | zero => intro _; exact ReflTransGen.refl
      | succ t ih =>
        intro ht
        refine ReflTransGen.tail (ih (by omega)) ?_
        rw [h49_run_succ, h49_step_some M _ (hlt t (by omega))]
        simp
    exact this T le_rfl

