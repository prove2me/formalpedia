-- Prove2me | solution 2 for OAI.SingleFold.Counter.eval_dom_iff_halts
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T19:30:27.401154+00:00
-- url     : https://prove2.me/submissions/1d0894d1-cf8e-438c-a3e4-6743a6e7f650

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/SingleFold/MacroMachine.lean:L390-L402
-- (upload_full_project.md Phase 4): solution for node OAI.SingleFold.Counter.eval_dom_iff_halts. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
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

-- ---- from OAI.NumberTheory.SingleFold.CounterMachine ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace SingleFold.Counter

section
variable {Q J : Type} [DecidableEq Q] [DecidableEq J]
omit [DecidableEq Q] in
lemma run_succ (M : Machine Q J) (d : J → ℕ) (t : ℕ) : run M d (t+1)=next M (run M d t) :=
  Function.iterate_succ_apply' _ _ _
variable [Fintype Q] [Fintype J]
end

open Packed
variable {Q J : Type} [Fintype Q] [Fintype J] [DecidableEq Q] [DecidableEq J]
variable {M : Machine Q J} {d : J → ℕ} {v : Witness Q J}
namespace System

section
variable (h : System M d v)
include h
end

section
variable (h : System M d v)
include h
end

variable (h : System M d v)
include h
end System
end SingleFold.Counter

end OAI

-- ---- from OAI.NumberTheory.SingleFold.MacroMachine ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace SingleFold.Counter
variable {Q J : Type} [DecidableEq Q] [DecidableEq J]
end SingleFold.Counter

namespace SingleFold.Macro

section
open Counter StateTransition Relation
variable {Q J : Type}
variable [DecidableEq J]
variable [DecidableEq Q]

end

section
open Counter StateTransition Relation
variable {Q J : Type} [DecidableEq Q] [DecidableEq J]
variable (M : Q → Instr Q J) (start : Q)
local notation "F" => Counter.step (compile M start)
end

open Counter StateTransition Relation
variable {Q J : Type} [DecidableEq Q] [DecidableEq J]
variable (M : Q → Instr Q J) (start : Q)
local notation "F" => Counter.step (compile M start)
end SingleFold.Macro

namespace SingleFold.Counter
open StateTransition Relation
variable {Q J : Type} [DecidableEq Q] [DecidableEq J]
omit [DecidableEq Q] in
lemma step_eq_none (M : Machine Q J) (c : Cfg Q J) : step M c=none ↔ c.state=M.halt := by
  rw [←M.halt_iff c.state]
  cases h : M.instr c.state <;> simp [step,h]
omit [DecidableEq Q] in
lemma reaches_iterate (M : Machine Q J) {c e : Cfg Q J} (h : Reaches (step M) c e) :
    ∃t,(next M)^[t] c=e := by
  induction h with
  | refl => exact ⟨0,rfl⟩
  | @tail d e h hd ih =>
    rcases ih with ⟨t,rfl⟩
    refine ⟨t+1,?_⟩
    rw [Function.iterate_succ_apply']
    change step M ((next M)^[t] c)=some e at hd
    unfold step at hd
    split at hd
    · contradiction
    · exact Option.some.inj hd
omit [DecidableEq Q] in
lemma reaches_run (M : Machine Q J) (d : J → ℕ) (t : ℕ) :
    Reaches (step M) ⟨M.start,d⟩ (run M d t) := by
  induction t with
  | zero => exact ReflTransGen.refl
  | succ t ih =>
    rw [run_succ]
    cases h : M.instr (run M d t).state with
    | halt => simpa only [next,h] using ih
    | inc j p => exact ih.tail (by simp [step,h])
    | test j pz pd => exact ih.tail (by simp [step,h])
lemma halts_iff_exists (M : Machine Q J) (d : J → ℕ) : Halts M d ↔ ∃t,(run M d t).state=M.halt := by
  constructor
  · rintro ⟨t,ht,_⟩; exact ⟨t,ht⟩
  · intro h
    exact ⟨Nat.find h,Nat.find_spec h,fun t ht=>Nat.find_min h ht⟩
lemma eval_dom_iff_halts (M : Machine Q J) (d : J → ℕ) :
    (eval (step M) ⟨M.start,d⟩).Dom ↔ Halts M d := by
  rw [halts_iff_exists]
  constructor
  · intro h
    obtain ⟨hr,hh⟩ := mem_eval.mp (Part.get_mem h)
    obtain ⟨t,ht⟩ := reaches_iterate M hr
    refine ⟨t,?_⟩
    have := (step_eq_none M _).mp hh
    simpa only [run,ht] using this
  · rintro ⟨t,ht⟩
    have h := mem_eval.mpr ⟨reaches_run M d t,(step_eq_none M _).mpr ht⟩
    exact Part.dom_iff_mem.mpr ⟨_,h⟩
end SingleFold.Counter

end OAI

-- ---- platform node ----
open OAI OAI.SingleFold OAI.SingleFold.Counter
open StateTransition Relation


theorem solution : type_of% @_root_.OAI.SingleFold.Counter.eval_dom_iff_halts := @_root_.OAI.SingleFold.Counter.eval_dom_iff_halts
