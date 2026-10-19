-- Prove2me | solution 1 for MIPRE.LowDegree.BinaryLinear.basisSolveProg_encoding
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T02:48:21.127204+00:00
-- url     : https://prove2.me/submissions/ff872032-cb41-4543-8867-6f572daaad02

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/LowDegree/BinarySolve.lean (solution of MIPRE.LowDegree.BinaryLinear.basisSolveProg_encoding);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Data.List.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_SAT_Circuit
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Fold
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryRepresentation
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryPolynomial
import Definitions.Def_MIPRE_Foundations_Cost_Binary
import Definitions.Def_MIPRE_Foundations_SAT_Formula
import Definitions.Def_MIPRE_Foundations_SAT_FmlLib
import Definitions.Def_MIPRE_Foundations_SAT_Flatten
import Definitions.Def_MIPRE_Foundations_Cost_Reader
import Definitions.Def_MIPRE_Foundations_SAT_FmlProg
import Definitions.Def_MIPRE_Foundations_SAT_ArrayProg
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryLinear
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryElimination
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryBasisProg
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryEchelon
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryEchelon_B
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryBasis
import Definitions.Def_MIPRE_Foundations_LowDegree_BinarySolve
import Definitions.Def_MIPRE_Foundations_LowDegree_BinarySolve_B
import Theorems.Thm_MIPRE_LowDegree_BinaryLinear_getD_vectorBits
import Theorems.Thm_MIPRE_LowDegree_BinaryLinear_insertRow_pivotBits
import Theorems.Thm_MIPRE_LowDegree_BinaryLinear_xorBits_vectorBits

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.LowDegree.BinaryLinear
section
open Cost Cost.PolyTimeFun Polynomial
/-- A raw XOR step is the corresponding operation on both typed vectors. -/
theorem reduceStep_rowBits {n t : ℕ} (r : Row n t) (p : Pivot n t) :
    reduceStep (rowBits r) (pivotBits p) = rowBits (typedReduceStep r p) := by
  unfold reduceStep pivotBits rowBits
  rw [getD_vectorBits]
  simp only [bit, decide_eq_true_eq, typedReduceStep]
  split_ifs
  · rw [xorBits_vectorBits, xorBits_vectorBits]
  · rfl
end
end MIPRE.LowDegree.BinaryLinear

namespace MIPRE.LowDegree.BinaryLinear
section
open Cost Cost.PolyTimeFun Polynomial
/-- The entire executable reduction agrees with typed binary elimination. -/
theorem reduceRows_rowBits {n t : ℕ} (b : List (Pivot n t)) (r : Row n t) :
    reduceRows (b.map pivotBits) (rowBits r) = rowBits (typedReduce b r) := by
  induction b generalizing r with
  | nil => rfl
  | cons p b ih =>
    change reduceRows (b.map pivotBits) (reduceStep (rowBits r) (pivotBits p)) = _
    rw [reduceStep_rowBits, ih]
    rfl
end
end MIPRE.LowDegree.BinaryLinear

namespace MIPRE.LowDegree.BinaryLinear
section
variable {n t : ℕ}
theorem fold_insertRow_pivotBits (rows : List (Row n t)) (b : List (Pivot n t)) :
    (rows.map rowBits).foldl insertRow (b.map pivotBits) =
      (rows.foldl typedInsert b).map pivotBits := by
  induction rows generalizing b with
  | nil => rfl
  | cons r rows ih =>
    simp only [List.map_cons, List.foldl_cons, insertRow_pivotBits, ih]
end
end MIPRE.LowDegree.BinaryLinear

namespace MIPRE.LowDegree.BinaryLinear
section
variable {n t : ℕ}
/-- The actual ambient program constructs precisely the typed binary basis. -/
theorem basisRowsProg_correct (rows : List (Row n t)) :
    basisRowsProg (rows.map rowBits) = (typedBasis rows).map pivotBits :=
  fold_insertRow_pivotBits rows []
end
end MIPRE.LowDegree.BinaryLinear

namespace MIPRE.LowDegree.BinaryLinear
section
open Cost Cost.PolyTimeFun
variable {n t : ℕ}
/-- Solver output is the canonical fixed-width encoding of its coefficient vector. -/
theorem solveBitsProg_encoding (b : List (Pivot n t)) (v : Fin n → ZMod 2) :
    solveBitsProg (unary t, b.map pivotBits, vectorBits v) =
      vectorBits (typedReduce b (v, 0)).2 := by
  have hz : List.replicate t false = vectorBits (0 : Fin t → ZMod 2) := by
    simp [vectorBits, bit]
  change (reduceRows (b.map pivotBits)
    (vectorBits v, List.replicate (unary t).length false)).2 = _
  rw [length_unary, hz]
  exact congrArg Prod.snd (reduceRows_rowBits b (v, 0))
end
end MIPRE.LowDegree.BinaryLinear

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.LowDegree.BinaryLinear
open Cost Cost.PolyTimeFun
variable {n t : ℕ}
theorem _root_.solution (rows : List (Row n t)) (v : Fin n → ZMod 2) :
    basisSolveProg (unary t, rows.map rowBits, vectorBits v) =
      vectorBits (typedReduce (typedBasis rows) (v, 0)).2 := by
  change solveBitsProg (unary t, basisRowsProg (rows.map rowBits), vectorBits v) = _
  rw [basisRowsProg_correct, solveBitsProg_encoding]
end MIPRE.LowDegree.BinaryLinear
