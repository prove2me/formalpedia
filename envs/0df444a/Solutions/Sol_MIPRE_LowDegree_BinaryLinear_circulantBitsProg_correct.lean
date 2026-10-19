-- Prove2me | solution 1 for MIPRE.LowDegree.BinaryLinear.circulantBitsProg_correct
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T03:26:17.082234+00:00
-- url     : https://prove2.me/submissions/59f0fc57-cdab-49ca-bf01-8c0ac7007a91

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/LowDegree/BinaryCirculantProg.lean (solution of MIPRE.LowDegree.BinaryLinear.circulantBitsProg_correct);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Rotate
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Matrix.Circulant
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
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryEchelon_B
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryBasis
import Definitions.Def_MIPRE_Foundations_LowDegree_BinarySolve
import Definitions.Def_MIPRE_Foundations_LowDegree_BinarySolve_B
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryMatrixSolve
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryMatrixSolve_B
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryMatrixInverse
import Definitions.Def_MIPRE_Foundations_LowDegree_SelfDualize
import Definitions.Def_MIPRE_Foundations_LowDegree_BinarySquareRoot
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryCirculant
import Definitions.Def_MIPRE_Foundations_Cost_Iterates
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryCirculantProg
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryCirculantProg_B
import Theorems.Thm_MIPRE_LowDegree_BinaryLinear_transposeBits_matrixBits

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.LowDegree.BinaryLinear
section
open Cost Cost.PolyTimeFun
theorem rotateLeftBits_eq_rotate (l : BitStr) : rotateLeftBits l = l.rotate 1 := by
  cases l <;> simp [rotateLeftBits, List.rotate_eq_rotate', List.rotate']
end
end MIPRE.LowDegree.BinaryLinear

namespace MIPRE.LowDegree.BinaryLinear
section
open Cost Cost.PolyTimeFun
theorem iterate_rotateRightBits (n : ℕ) (l : BitStr) :
    rotateRightBits^[n] l = (l.reverse.rotate n).reverse := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih]
    simp only [rotateRightBits, List.reverse_reverse, rotateLeftBits_eq_rotate, List.rotate_rotate]
end
end MIPRE.LowDegree.BinaryLinear

namespace MIPRE.LowDegree.BinaryLinear
section
open Cost Cost.PolyTimeFun
theorem reverse_vectorBits {k : ℕ} (v : Fin k → ZMod 2) :
    (vectorBits v).reverse = vectorBits (fun i => v i.rev) := by
  apply List.ext_getElem
  · simp [vectorBits]
  · intro i hi hj
    simp [vectorBits, List.getElem_reverse, Fin.rev, Nat.sub_sub, Nat.add_comm]
end
end MIPRE.LowDegree.BinaryLinear

namespace MIPRE.LowDegree.BinaryLinear
section
open Cost Cost.PolyTimeFun
theorem rotate_vectorBits {k : ℕ} [NeZero k] (v : Fin k → ZMod 2) (j : Fin k) :
    (vectorBits v).rotate j = vectorBits (fun i => v (i + j)) := by
  apply List.ext_getElem
  · simp [vectorBits]
  · intro i hi hj
    simp only [List.getElem_rotate, vectorBits, List.length_ofFn, List.getElem_ofFn]
    rfl
end
end MIPRE.LowDegree.BinaryLinear

namespace MIPRE.LowDegree.BinaryLinear
section
open Cost Cost.PolyTimeFun
/-- Right rotation is translation by the negative column index. -/
theorem iterate_rotateRightBits_vectorBits {k : ℕ} [NeZero k]
    (v : Fin k → ZMod 2) (j : Fin k) :
    rotateRightBits^[j] (vectorBits v) = vectorBits (fun i => v (i - j)) := by
  rw [iterate_rotateRightBits, reverse_vectorBits, rotate_vectorBits, reverse_vectorBits]
  congr 1
  funext i
  rw [Fin.rev_add, Fin.rev_rev]
end
end MIPRE.LowDegree.BinaryLinear

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.LowDegree.BinaryLinear
open Cost Cost.PolyTimeFun
theorem _root_.solution {k : ℕ} [NeZero k] (v : Fin k → ZMod 2) :
    circulantBitsProg (vectorBits v) = matrixBits (Matrix.circulant v) := by
  have hc : recordIterates rotateRightBits (unary k) (vectorBits v) =
      matrixBits (Matrix.circulant v).transpose := by
    unfold recordIterates matrixBits
    simp only [length_unary]
    apply congrArg List.ofFn
    funext j
    exact iterate_rotateRightBits_vectorBits v j
  change transposeBits (unary (vectorBits v).length).length
    (recordIterates rotateRightBits (unary (vectorBits v).length) (vectorBits v)) = _
  rw [show (vectorBits v).length = k from List.length_ofFn, length_unary, hc,
    transposeBits_matrixBits, Matrix.transpose_transpose]
end MIPRE.LowDegree.BinaryLinear
