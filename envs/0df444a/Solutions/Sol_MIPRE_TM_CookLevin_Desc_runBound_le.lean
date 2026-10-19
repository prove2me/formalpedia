-- Prove2me | solution 1 for MIPRE.TM.CookLevin.Desc.runBound_le
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:48:28.364703+00:00
-- url     : https://prove2.me/submissions/ac1e03d0-3af4-44f9-9b02-d5c0c265bcd2

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/TM/CookLevin/Params.lean (solution of MIPRE.TM.CookLevin.Desc.runBound_le);
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

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost
/-- `a ≤ c · M ^ i` and `b ≤ d · M ^ j` give `a · b ≤ c d · M ^ (i + j)`. -/
theorem mul_le_mul_pow {a b c d i j M : ℕ} (ha : a ≤ c * M ^ i) (hb : b ≤ d * M ^ j) :
    a * b ≤ c * d * M ^ (i + j) := by
  calc a * b ≤ c * M ^ i * (d * M ^ j) := Nat.mul_le_mul ha hb
    _ = c * d * M ^ (i + j) := by ring
end
end MIPRE.TM.CookLevin.Desc

namespace MIPRE.TM.CookLevin.Desc
section
open Interp SAT Cost
/-- Raising the exponent of a majorant. -/
theorem le_mul_pow_of_le {a c i j M : ℕ} (hM : 1 ≤ M) (h : a ≤ c * M ^ i) (hij : i ≤ j) :
    a ≤ c * M ^ j :=
  h.trans (Nat.mul_le_mul_left c (Nat.pow_le_pow_right hM hij))
end
end MIPRE.TM.CookLevin.Desc

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.TM.CookLevin.Desc
open Interp SAT Cost
variable (D : Prog) (n T Q σ : ℕ) (x y a b : BitStr)
theorem _root_.solution (hV : Valid D n T Q σ x y) (ha : a.length ≤ T) (hb : b.length ≤ T) :
    runBound D n x y a b T ≤ 400000 * (T + σ + 1) ^ 5 := by
  set M := T + σ + 1 with hM
  clear_value M
  have h1 : 1 ≤ M := by omega
  have hM1 : M ^ 1 = M := pow_one M
  have hTM : T ≤ 1 * M ^ 1 := by rw [hM1]; omega
  have hσM : σ ≤ 1 * M ^ 1 := by rw [hM1]; omega
  -- the sizes of the pieces of the input
  have hD : esize D ≤ 1 * M ^ 1 := by rw [hM1]; have := hV.size_le; omega
  have hn : esize n ≤ 3 * M ^ 1 := by
    rw [hM1]
    have h2 := esize_nat_le n
    have h3 := hV.logn_le
    omega
  have hx : esize x ≤ 5 * M ^ 1 := by
    rw [hM1]
    have h2 := esize_bitStr_le x
    have h3 := hV.x_le
    have h4 := hV.q_le
    omega
  have hy : esize y ≤ 5 * M ^ 1 := by
    rw [hM1]
    have h2 := esize_bitStr_le y
    have h3 := hV.y_le
    have h4 := hV.q_le
    omega
  have hae : esize a ≤ 5 * M ^ 1 := by
    rw [hM1]
    have h2 := esize_bitStr_le a
    omega
  have hbe : esize b ≤ 5 * M ^ 1 := by
    rw [hM1]
    have h2 := esize_bitStr_le b
    omega
  -- the value bound
  have hV0 : V0 n x y a b T ≤ 27 * M ^ 1 := by
    rw [hM1] at hTM hn hx hy hae hbe ⊢
    show max (esize (n, x, y, a, b)) T ≤ 27 * M
    have he : esize (n, x, y, a, b) = esize n + esize x + esize y + esize a + esize b + 4 := by
      simp only [esize_prod]; omega
    omega
  have hL : 1 + 2 * T ≤ 3 * M ^ 1 := by rw [hM1]; omega
  -- the size bound along the run
  have hZ0 : Z0 D n x y a b T ≤ 231 * M ^ 3 := by
    show szBound (V0 n x y a b T) (1 + 2 * T) (esize D) T ≤ _
    have e1 : (1 + 2 * T) * V0 n x y a b T ≤ 81 * M ^ 2 := by
      have := mul_le_mul_pow hL hV0
      norm_num at this
      exact this
    have hin : V0 n x y a b T + esize D + (1 + 2 * T) * V0 n x y a b T + (1 + 2 * T) + 4
        ≤ 116 * M ^ 2 := by
      have h4 : (4 : ℕ) ≤ 4 * M ^ 2 := by
        have : (1 : ℕ) ≤ M ^ 2 := Nat.one_le_pow _ _ (by omega)
        omega
      have hV0' : V0 n x y a b T ≤ 27 * M ^ 2 := le_mul_pow_of_le h1 hV0 (by omega)
      have hD' : esize D ≤ 1 * M ^ 2 := le_mul_pow_of_le h1 hD (by omega)
      have hL' : 1 + 2 * T ≤ 3 * M ^ 2 := le_mul_pow_of_le h1 hL (by omega)
      omega
    have e2 : T * (V0 n x y a b T + esize D + (1 + 2 * T) * V0 n x y a b T + (1 + 2 * T) + 4)
        ≤ 116 * M ^ 3 := by
      have h := mul_le_mul_pow hTM hin
      norm_num at h
      exact h
    have hV0' : V0 n x y a b T ≤ 27 * M ^ 3 := le_mul_pow_of_le h1 hV0 (by omega)
    have hD' : esize D ≤ 1 * M ^ 3 := le_mul_pow_of_le h1 hD (by omega)
    have hL' : 1 + 2 * T ≤ 3 * M ^ 3 := le_mul_pow_of_le h1 hL (by omega)
    have e1' : (1 + 2 * T) * V0 n x y a b T ≤ 81 * M ^ 3 := le_mul_pow_of_le h1 e1 (by omega)
    have h2 : (2 : ℕ) ≤ 2 * M ^ 3 := by
      have : (1 : ℕ) ≤ M ^ 3 := Nat.one_le_pow _ _ (by omega)
      omega
    have h1' : (1 : ℕ) ≤ 1 * M ^ 3 := by
      have : (1 : ℕ) ≤ M ^ 3 := Nat.one_le_pow _ _ (by omega)
      omega
    show (V0 n x y a b T + esize D + 2) + ((1 + 2 * T) * V0 n x y a b T + (1 + 2 * T)) +
      T * (V0 n x y a b T + esize D + (1 + 2 * T) * V0 n x y a b T + (1 + 2 * T) + 4) + 1 ≤ _
    omega
  -- the per-step bound
  have hxl : 3 * T * Z0 D n x y a b T ≤ 693 * M ^ 4 := by
    have h3T : 3 * T ≤ 3 * M ^ 1 := by rw [hM1]; omega
    have := mul_le_mul_pow h3T hZ0
    norm_num at this
    exact this
  have hstep : stepB (Z0 D n x y a b T) (3 * T * Z0 D n x y a b T) ≤ 100000 * M ^ 4 := by
    show 100 * (Z0 D n x y a b T + 3 * T * Z0 D n x y a b T + 1) + Z0 D n x y a b T + 30 ≤ _
    have hZ0' : Z0 D n x y a b T ≤ 231 * M ^ 4 := le_mul_pow_of_le h1 hZ0 (by omega)
    have h30 : (31 : ℕ) ≤ 31 * M ^ 4 := by
      have : (1 : ℕ) ≤ M ^ 4 := Nat.one_le_pow _ _ (by omega)
      omega
    omega
  have hmain : 3 * T * stepB (Z0 D n x y a b T) (3 * T * Z0 D n x y a b T) ≤ 300000 * M ^ 5 := by
    have h3T : 3 * T ≤ 3 * M ^ 1 := by rw [hM1]; omega
    have := mul_le_mul_pow h3T hstep
    norm_num at this
    exact this
  -- the initialization
  have hinit : initBound D n x y a b T ≤ 73 * M ^ 1 := by
    rw [hM1] at hTM hD hn hx hy ⊢
    show 3 * T + 8 * (a.length + b.length) + (S D.toData).length + (S (encode n)).length +
      (S (encode x)).length + (S (encode y)).length + 40 ≤ 73 * M
    rw [length_S, length_S, length_S, length_S]
    have e1 : D.toData.size = esize D := rfl
    have e2 : (encode n : Data).size = esize n := rfl
    have e3 : (encode x : Data).size = esize x := rfl
    have e4 : (encode y : Data).size = esize y := rfl
    omega
  -- putting it together
  have hinit' : initBound D n x y a b T ≤ 73 * M ^ 5 := le_mul_pow_of_le h1 hinit (by omega)
  have hV0'' : V0 n x y a b T ≤ 27 * M ^ 5 := le_mul_pow_of_le h1 hV0 (by omega)
  have h16 : (16 : ℕ) ≤ 16 * M ^ 5 := by
    have : (1 : ℕ) ≤ M ^ 5 := Nat.one_le_pow _ _ (by omega)
    omega
  show initBound D n x y a b T + 3 * T * stepB (Z0 D n x y a b T) (3 * T * Z0 D n x y a b T) +
    V0 n x y a b T + 16 ≤ _
  omega
end MIPRE.TM.CookLevin.Desc
