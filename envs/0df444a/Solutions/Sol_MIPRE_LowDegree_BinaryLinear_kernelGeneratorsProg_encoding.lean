-- Prove2me | solution 1 for MIPRE.LowDegree.BinaryLinear.kernelGeneratorsProg_encoding
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T02:44:49.185186+00:00
-- url     : https://prove2.me/submissions/0ac72da6-d880-4b9b-b059-4e3c8f641691

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/LowDegree/BinaryKernel.lean (solution of MIPRE.LowDegree.BinaryLinear.kernelGeneratorsProg_encoding);
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
import Mathlib.LinearAlgebra.Matrix.ToLin
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
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryBasis
import Definitions.Def_MIPRE_Foundations_LowDegree_BinarySolve
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryMatrixSolve
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryKernel
import Theorems.Thm_MIPRE_LowDegree_BinaryLinear_coordinateRows_matrixBits
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
theorem kernelMap_apply {m n : ℕ} (A : Matrix (Fin m) (Fin n) (ZMod 2))
    (x : Fin n → ZMod 2) :
    kernelMap A x = (typedReduce (typedBasis (columnRows A)) (A.mulVec x, x)).2 := by
  simp [kernelMap]
end
end MIPRE.LowDegree.BinaryLinear

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.LowDegree.BinaryLinear
open Cost Cost.PolyTimeFun
variable {n t : ℕ}
theorem _root_.solution {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) (ZMod 2)) :
    kernelGeneratorsProg (unary n, matrixBits A) =
      List.ofFn (fun j : Fin n => vectorBits (kernelMap A (Pi.single j 1))) := by
  change ((coordinateRows (transposeBits (unary n).length (matrixBits A))).map
    (fun r => reduceRows (basisRowsProg (coordinateRows
      (transposeBits (unary n).length (matrixBits A)))) r)).map Prod.snd = _
  rw [length_unary, coordinateRows_matrixBits, basisRowsProg_correct, List.map_map,
    List.map_map]
  simp only [columnRows, List.map_ofFn]
  apply congrArg List.ofFn
  funext j
  change (reduceRows ((typedBasis (columnRows A)).map pivotBits)
    (rowBits (A.col j, Pi.single j 1))).2 = _
  rw [reduceRows_rowBits]
  change vectorBits (typedReduce (typedBasis (columnRows A)) (A.col j, Pi.single j 1)).2 = _
  rw [kernelMap_apply, Matrix.mulVec_single_one]
end MIPRE.LowDegree.BinaryLinear
