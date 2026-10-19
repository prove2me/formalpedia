-- Prove2me | solution 1 for MIPRE.TM.CookLevin.Desc.tapeSpec
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T02:26:05.951586+00:00
-- url     : https://prove2.me/submissions/963b9326-dd38-44fc-9589-2e7e38f04287

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/TM/CookLevin/Describer.lean (solution of MIPRE.TM.CookLevin.Desc.tapeSpec);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Computability.Language
import Mathlib.Computability.Primrec.List
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Int.Interval
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Sign.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Pi
import Mathlib.Logic.Denumerable
import Mathlib.Logic.Function.Iterate
import Mathlib.Logic.Relation
import Mathlib.Tactic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_SAT_Circuit
import Definitions.Def_MIPRE_Foundations_SAT_Cnf
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_CL_Closure
import Definitions.Def_MIPRE_Foundations_CL_Closure_B
import Definitions.Def_MIPRE_Foundations_CL_Sampler
import Definitions.Def_MIPRE_Foundations_Verifier
import Definitions.Def_MIPRE_Foundations_SAT_Succinct
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Fold
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_Cost_Codable_B
import Definitions.Def_MIPRE_Foundations_Cost_Binary
import Definitions.Def_MIPRE_Foundations_SAT_Formula
import Definitions.Def_MIPRE_Foundations_SAT_FmlLib
import Definitions.Def_MIPRE_Foundations_Cost_Machine_B
import Definitions.Def_MIPRE_Foundations_Cost_MachineData_B
import Definitions.Def_MIPRE_Foundations_Cost_MachineBound_B
import Definitions.Def_MIPRE_Cslib_Foundations_Data_RelatesInSteps
import Definitions.Def_MIPRE_Cslib_Computability_Machines_Turing_MultiTape_Deterministic
import Definitions.Def_MIPRE_TM_MultiInput_Deterministic
import Definitions.Def_MIPRE_TM_CookLevin_Local
import Definitions.Def_MIPRE_Foundations_SAT_Tseitin
import Definitions.Def_MIPRE_TM_CookLevin_Tableau
import Definitions.Def_MIPRE_TM_Interp_Instr
import Definitions.Def_MIPRE_TM_Interp_Machine
import Definitions.Def_MIPRE_TM_CookLevin_Layout
import Definitions.Def_MIPRE_TM_CookLevin_FieldFml
import Definitions.Def_MIPRE_TM_CookLevin_Kinds
import Definitions.Def_MIPRE_TM_CookLevin_Families
import Definitions.Def_MIPRE_TM_CookLevin_Window
import Definitions.Def_MIPRE_TM_CookLevin_FamilyFml
import Definitions.Def_MIPRE_TM_Interp_Tape
import Definitions.Def_MIPRE_TM_Interp_Reach
import Definitions.Def_MIPRE_TM_Interp_Routines
import Definitions.Def_MIPRE_TM_Interp_Repr
import Definitions.Def_MIPRE_TM_Interp_CopyTree
import Definitions.Def_MIPRE_TM_Interp_GetEnv
import Definitions.Def_MIPRE_TM_Interp_Desc
import Definitions.Def_MIPRE_TM_Interp_Step
import Definitions.Def_MIPRE_TM_Interp_InputRoutines
import Definitions.Def_MIPRE_TM_Interp_Run
import Definitions.Def_MIPRE_Foundations_SAT_Table
import Definitions.Def_MIPRE_TM_CookLevin_Params
import Definitions.Def_MIPRE_TM_CookLevin_AnsEnd
import Definitions.Def_MIPRE_TM_CookLevin_Index
import Definitions.Def_MIPRE_TM_CookLevin_Describer
import Theorems.Thm_MIPRE_TM_CookLevin_Desc_eval_cellValF
import Theorems.Thm_MIPRE_TM_CookLevin_Desc_eval_unaryValF

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Fml
theorem Bool.eq_decide_of_iff {b : Bool} {P : Prop} [Decidable P] (h : b = true ↔ P) :
    b = decide P := by
  cases b
  · simp only [Bool.false_eq_true, false_iff] at h
    simp [h]
  · simp only [true_iff] at h
    simp [h]
end
end MIPRE.TM.CookLevin.Desc

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.TM.CookLevin.Desc
open Interp SAT Cost Fml
theorem _root_.solution (e T : ℕ) (D : Prog) (n : ℕ) (x y : BitStr) (G : ℕ) {A : FieldsF}
    (hA : A.Lengths e G) (hT : T ≤ Sof e) (hlen : FixedLen e D n T x y) :
    TapeSpec e A (fixedOf D n T x y) (tabsOf e T D n x y A) := by
  have hval : ∀ (j : Fin 7) (s : List Sym), fixedOf D n T x y j = some s →
      ∀ x' : ℕ → Bool, (cellValF e A (codesOf s)).eval x' =
        decide ((evalFields A x').v = cellCode s (Sof e) (evalFields A x').p) := by
    intro j s hj x'
    exact Bool.eq_decide_of_iff (eval_cellValF e G hA x' s (hlen j s hj))
  constructor
  · intro jv hjv
    simp only [tabsOf, List.mem_cons, List.not_mem_nil, or_false] at hjv
    rcases hjv with rfl | rfl | rfl | rfl | rfl
    · exact ⟨0, S D.toData, rfl, by simp [fixedOf], hval 0 _ (by simp [fixedOf])⟩
    · exact ⟨1, S (encode n), rfl, by simp [fixedOf], hval 1 _ (by simp [fixedOf])⟩
    · refine ⟨2, List.replicate T .one, rfl, by simp [fixedOf], fun x' => ?_⟩
      exact Bool.eq_decide_of_iff (eval_unaryValF e G hA x' T hT)
    · exact ⟨3, S (encode x), rfl, by simp [fixedOf], hval 3 _ (by simp [fixedOf])⟩
    · exact ⟨4, S (encode y), rfl, by simp [fixedOf], hval 4 _ (by simp [fixedOf])⟩
  · intro j s hj
    fin_cases j
    · exact ⟨cellValF e A (codesOf (S D.toData)), by simp [tabsOf]⟩
    · exact ⟨cellValF e A (codesOf (S (encode n))), by simp [tabsOf]⟩
    · exact ⟨unaryValF e T A, by simp [tabsOf]⟩
    · exact ⟨cellValF e A (codesOf (S (encode x))), by simp [tabsOf]⟩
    · exact ⟨cellValF e A (codesOf (S (encode y))), by simp [tabsOf]⟩
    · simp [fixedOf] at hj
    · simp [fixedOf] at hj
end MIPRE.TM.CookLevin.Desc
