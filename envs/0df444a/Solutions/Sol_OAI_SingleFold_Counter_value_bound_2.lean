-- Prove2me | solution 2 for OAI.SingleFold.Counter.value_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T19:06:05.525858+00:00
-- url     : https://prove2.me/submissions/8b24ab4e-760c-471f-a28a-9f7e132a95ed

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/SingleFold/CounterMachine.lean:L49-L69
-- (upload_full_project.md Phase 4): solution for node OAI.SingleFold.Counter.value_bound. The node keeps its source
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

-- ---- from OAI.NumberTheory.SingleFold.CounterMachine ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace SingleFold.Counter

section
variable {Q J : Type} [DecidableEq Q] [DecidableEq J]
omit [DecidableEq Q] in
lemma run_succ (M : Machine Q J) (d : J → ℕ) (t : ℕ) : run M d (t+1)=next M (run M d t) :=
  Function.iterate_succ_apply' _ _ _
omit [DecidableEq Q] in
lemma value_bound (M : Machine Q J) (d : J → ℕ) (t : ℕ) (j : J) : (run M d t).value j ≤ d j+t := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [run_succ,next]
    split
    · omega
    · rename_i k p hk
      dsimp
      by_cases h : j=k
      · subst j; simp; omega
      · simp [Function.update_of_ne h]; omega
    · rename_i k p0 pd hk
      split
      · change (run M d t).value j ≤ d j+(t+1)
        omega
      · dsimp
        by_cases h : j=k
        · subst j; simp; omega
        · simp [Function.update_of_ne h]; omega

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

-- ---- platform node ----
open OAI OAI.SingleFold OAI.SingleFold.Counter


theorem solution : type_of% @_root_.OAI.SingleFold.Counter.value_bound := @_root_.OAI.SingleFold.Counter.value_bound
