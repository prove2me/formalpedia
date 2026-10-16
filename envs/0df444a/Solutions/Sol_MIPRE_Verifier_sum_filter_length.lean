-- Prove2me | solution 1 for MIPRE.Verifier.sum_filter_length
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-15T19:47:52.626875+00:00
-- url     : https://prove2.me/submissions/4f23f76f-a9f9-41f2-9c7c-ab599f08f708

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Halting/Tabulate.lean (solution of MIPRE.Verifier.sum_filter_length);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Computability.Partrec
import Mathlib.Computability.PartrecBasis
import Mathlib.Computability.PartrecCode
import Mathlib.Computability.Primrec.List
import Mathlib.Computability.RE
import Mathlib.Computability.TuringMachine.Config
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Basic
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Pi
import Mathlib.Logic.Denumerable
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_CL_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_CL_Sampler
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_HaltingGameValue
import Definitions.Def_MIPRE_Foundations_GameDescription
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Toolkit
import Definitions.Def_MIPRE_Foundations_Cost_Toolkit_B
import Definitions.Def_MIPRE_Foundations_Cost_Machine
import Definitions.Def_MIPRE_Foundations_Cost_Machine_B
import Definitions.Def_MIPRE_Foundations_Cost_Loops
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Codable
import Definitions.Def_MIPRE_Foundations_Cost_Codable_B
import Definitions.Def_MIPRE_Foundations_Cost_MachineData
import Definitions.Def_MIPRE_Foundations_Cost_MachineData_B
import Definitions.Def_MIPRE_Foundations_Cost_Interpreter
import Definitions.Def_MIPRE_Foundations_Cost_Interpreter_B
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_MachineBound
import Definitions.Def_MIPRE_Foundations_Cost_MachineBound_B
import Definitions.Def_MIPRE_Foundations_Cost_Universal
import Definitions.Def_MIPRE_Foundations_Cost_Universal_B
import Definitions.Def_MIPRE_Foundations_Cost_Kleene
import Definitions.Def_MIPRE_Foundations_Cost_Kleene_B
import Definitions.Def_MIPRE_Foundations_Cost_FromPartrec
import Definitions.Def_MIPRE_Foundations_Cost_FromPartrec_B
import Definitions.Def_MIPRE_Foundations_Cost_Partrec
import Definitions.Def_MIPRE_Foundations_Cost_Partrec_B
import Definitions.Def_MIPRE_Foundations_Cost_Semidecide
import Definitions.Def_MIPRE_Foundations_GameDouble
import Definitions.Def_MIPRE_Foundations_Verifier
import Definitions.Def_MIPRE_Foundations_GapCompression
import Definitions.Def_MIPRE_Foundations_VerifierValue
import Definitions.Def_MIPRE_Foundations_Halting_Freeze
import Definitions.Def_MIPRE_Foundations_Halting_Classes
import Definitions.Def_MIPRE_Foundations_Halting_Descriptions
import Definitions.Def_MIPRE_Foundations_Cost_Numeric
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_Halting_Lists
import Definitions.Def_MIPRE_Foundations_Cost_Growth
import Definitions.Def_MIPRE_Foundations_Halting_Arith
import Definitions.Def_MIPRE_Foundations_Halting_Wrapper
import Definitions.Def_MIPRE_Foundations_Halting_Enumerate
import Definitions.Def_MIPRE_Foundations_Cost_BoundedEval
import Definitions.Def_MIPRE_Foundations_Halting_Tabulate

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Verifier
open Cost
open HaltingGameValue (GameData)
theorem _root_.solution {N : ℕ} (fA fB : BitStr → ℕ) (l : List BitStr)
    (hA : ∀ z ∈ l, fA z < N) (hB : ∀ z ∈ l, fB z < N) :
    ∑ x : Fin N, ∑ y : Fin N,
      (l.filter fun z => decide (fA z = x.val ∧ fB z = y.val)).length = l.length := by
  induction l with
  | nil => simp
  | cons z l ih =>
    have hAz : fA z < N := hA z (by simp)
    have hBz : fB z < N := hB z (by simp)
    have hstep : ∀ x y : Fin N,
        ((z :: l).filter fun w => decide (fA w = x.val ∧ fB w = y.val)).length =
          (if fA z = x.val ∧ fB z = y.val then 1 else 0) +
            (l.filter fun w => decide (fA w = x.val ∧ fB w = y.val)).length := by
      intro x y
      rw [List.filter_cons]
      by_cases h : fA z = x.val ∧ fB z = y.val
      · rw [if_pos (by simpa using h), List.length_cons, if_pos h]; omega
      · rw [if_neg (by simpa using h), if_neg h]; omega
    simp only [hstep, Finset.sum_add_distrib]
    rw [ih (fun w hw => hA w (by simp [hw])) (fun w hw => hB w (by simp [hw])),
      List.length_cons]
    have hone : ∑ x : Fin N, ∑ y : Fin N,
        (if fA z = x.val ∧ fB z = y.val then 1 else 0) = 1 := by
      rw [Finset.sum_eq_single (⟨fA z, hAz⟩ : Fin N)]
      · rw [Finset.sum_eq_single (⟨fB z, hBz⟩ : Fin N)]
        · simp
        · intro b _ hb
          exact if_neg fun h => hb (Fin.ext h.2.symm)
        · intro hmem; exact absurd (Finset.mem_univ _) hmem
      · intro a _ ha
        exact Finset.sum_eq_zero fun b _ => if_neg fun h => ha (Fin.ext h.1.symm)
      · intro hmem; exact absurd (Finset.mem_univ _) hmem
    omega
end MIPRE.Verifier
