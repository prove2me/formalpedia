-- Prove2me | solution 1 for MIPRE.TM.CookLevin.Desc.le_roundUp
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T02:46:44.463287+00:00
-- url     : https://prove2.me/submissions/3c489c52-b829-4d72-b161-9e0c2dad0106

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/TM/CookLevin/Assemble.lean (solution of MIPRE.TM.CookLevin.Desc.le_roundUp);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Degree
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
import Definitions.Def_MIPRE_Foundations_SAT_Flatten
import Definitions.Def_MIPRE_Foundations_Cost_Reader
import Definitions.Def_MIPRE_Foundations_SAT_FmlProg
import Definitions.Def_MIPRE_Foundations_Cost_TreeBits
import Definitions.Def_MIPRE_Foundations_Cost_Machine_B
import Definitions.Def_MIPRE_Foundations_Cost_MachineData_B
import Definitions.Def_MIPRE_Foundations_Cost_MachineBound_B
import Definitions.Def_MIPRE_Foundations_Cost_Growth
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
import Definitions.Def_MIPRE_TM_CookLevin_LayoutProg
import Definitions.Def_MIPRE_TM_CookLevin_FieldProg
import Definitions.Def_MIPRE_TM_CookLevin_FamilyProg
import Definitions.Def_MIPRE_TM_CookLevin_DescProg
import Definitions.Def_MIPRE_TM_CookLevin_Semantics
import Definitions.Def_MIPRE_TM_CookLevin_Correct
import Definitions.Def_MIPRE_TM_CookLevin_Sound
import Definitions.Def_MIPRE_TM_CookLevin_Sat
import Definitions.Def_MIPRE_TM_CookLevin_Assemble

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost Cost.PolyTimeFun
theorem L_lt (n T Q σ : ℕ) : LOf n T Q σ + 1 ≤ 5 * 2 ^ rParam n T Q σ := by
  have h0 : 0 < (2 : ℕ) ^ rParam n T Q σ := Nat.two_pow_pos _
  have h1 : Nat.size n < 2 ^ rParam n T Q σ :=
    lt_of_lt_of_le (Nat.lt_size_self _) (Nat.pow_le_pow_right (by omega) (by unfold rParam; omega))
  have h2 : Nat.size T < 2 ^ rParam n T Q σ :=
    lt_of_lt_of_le (Nat.lt_size_self _) (Nat.pow_le_pow_right (by omega) (by unfold rParam; omega))
  have h3 : Q < 2 ^ rParam n T Q σ :=
    lt_of_lt_of_le (Nat.lt_size_self _) (Nat.pow_le_pow_right (by omega) (by unfold rParam; omega))
  have h4 : σ < 2 ^ rParam n T Q σ :=
    lt_of_lt_of_le (Nat.lt_size_self _) (Nat.pow_le_pow_right (by omega) (by unfold rParam; omega))
  unfold LOf
  omega
end
end MIPRE.TM.CookLevin.Desc

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.TM.CookLevin.Desc
open Interp SAT Cost Cost.PolyTimeFun
theorem _root_.solution (P : Polynomial ℕ) (n T Q σ : ℕ) :
    P.eval (LOf n T Q σ) ≤ roundUp P n T Q σ := by
  have h1 : P.eval (LOf n T Q σ) ≤ P.eval (LOf n T Q σ + 1) :=
    polynomial_eval_mono _ (by omega)
  have h2 : P.eval (LOf n T Q σ + 1) ≤ roundA P * (LOf n T Q σ + 1) ^ roundK P :=
    polynomial_eval_le_sum_coeff_mul_pow P (by omega)
  have h3 : (LOf n T Q σ + 1) ^ roundK P ≤ (5 * 2 ^ rParam n T Q σ) ^ roundK P :=
    Nat.pow_le_pow_left (L_lt n T Q σ) _
  have h4 : ((5 * 2 ^ rParam n T Q σ) ^ roundK P : ℕ) =
      5 ^ roundK P * 2 ^ (roundK P * rParam n T Q σ) := by
    rw [mul_pow, ← pow_mul, Nat.mul_comm (roundK P)]
  have h5 : roundA P * 5 ^ roundK P < 2 ^ roundC P := Nat.lt_size_self _
  calc P.eval (LOf n T Q σ) ≤ roundA P * (LOf n T Q σ + 1) ^ roundK P := h1.trans h2
    _ ≤ roundA P * (5 ^ roundK P * 2 ^ (roundK P * rParam n T Q σ)) := by
        rw [← h4]; exact Nat.mul_le_mul_left _ h3
    _ = roundA P * 5 ^ roundK P * 2 ^ (roundK P * rParam n T Q σ) := by ring
    _ ≤ 2 ^ roundC P * 2 ^ (roundK P * rParam n T Q σ) := Nat.mul_le_mul_right _ h5.le
    _ = roundUp P n T Q σ := by rw [roundUp, pow_add, Nat.mul_comm]
end MIPRE.TM.CookLevin.Desc
