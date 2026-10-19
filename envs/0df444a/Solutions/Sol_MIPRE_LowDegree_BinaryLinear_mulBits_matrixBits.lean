-- Prove2me | solution 1 for MIPRE.LowDegree.BinaryLinear.mulBits_matrixBits
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T02:22:33.778856+00:00
-- url     : https://prove2.me/submissions/1c0ec2d8-85c2-4ceb-bee5-45693383f1a8

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/LowDegree/BinaryLinear.lean (solution of MIPRE.LowDegree.BinaryLinear.mulBits_matrixBits);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.CharP.Two
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
import Theorems.Thm_MIPRE_LowDegree_BinaryLinear_transposeBits_matrixBits

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.LowDegree.BinaryLinear
section
open Cost Cost.PolyTimeFun
theorem ofBool_injective : Function.Injective (ofBool : Bool → ZMod 2) := by
  intro a b h
  have := congrArg bit h
  simpa using this
end
end MIPRE.LowDegree.BinaryLinear

namespace MIPRE.LowDegree.BinaryLinear
section
open Cost Cost.PolyTimeFun
theorem ofBool_xor (a b : Bool) :
    (ofBool (a ^^ b) : ZMod 2) = ofBool a + ofBool b := by
  cases a <;> cases b <;> decide
end
end MIPRE.LowDegree.BinaryLinear

namespace MIPRE.LowDegree.BinaryLinear
section
open Cost Cost.PolyTimeFun
theorem ofBool_and (a b : Bool) :
    (ofBool (a && b) : ZMod 2) = ofBool a * ofBool b := by
  cases a <;> cases b <;> decide
end
end MIPRE.LowDegree.BinaryLinear

namespace MIPRE.LowDegree.BinaryLinear
section
open Cost Cost.PolyTimeFun
theorem ofBool_fold_dotStep (l : List (Bool × Bool)) (b : Bool) :
    (ofBool (l.foldl dotStep b) : ZMod 2) =
      ofBool b + (l.map (fun p => (ofBool p.1 : ZMod 2) * ofBool p.2)).sum := by
  induction l generalizing b with
  | nil => simp
  | cons p l ih =>
    rw [List.foldl_cons, ih]
    simp only [dotStep, ofBool_xor, ofBool_and, List.map_cons, List.sum_cons]
    ring
end
end MIPRE.LowDegree.BinaryLinear

namespace MIPRE.LowDegree.BinaryLinear
section
open Cost Cost.PolyTimeFun
theorem ofBool_dotBits (a b : BitStr) :
    (ofBool (dotBits a b) : ZMod 2) =
      ((a.zip b).map (fun p => (ofBool p.1 : ZMod 2) * ofBool p.2)).sum := by
  rw [dotBits, ofBool_fold_dotStep]
  simp [ofBool]
end
end MIPRE.LowDegree.BinaryLinear

namespace MIPRE.LowDegree.BinaryLinear
section
open Cost Cost.PolyTimeFun
theorem zip_vectorBits {n : ℕ} (v w : Fin n → ZMod 2) :
    (vectorBits v).zip (vectorBits w) = List.ofFn (fun i => (bit (v i), bit (w i))) := by
  apply List.ext_getElem
  · simp [vectorBits]
  · intro i hi hj
    simp [vectorBits]
end
end MIPRE.LowDegree.BinaryLinear

namespace MIPRE.LowDegree.BinaryLinear
section
open Cost Cost.PolyTimeFun
/-- The raw parity circuit computes the exact binary dot product. -/
theorem dotBits_vectorBits {n : ℕ} (v w : Fin n → ZMod 2) :
    dotBits (vectorBits v) (vectorBits w) = bit (∑ i, v i * w i) := by
  apply ofBool_injective
  rw [ofBool_dotBits, zip_vectorBits, ofBool_bit]
  simp only [List.map_ofFn, List.sum_ofFn, Function.comp_apply, ofBool_bit]
end
end MIPRE.LowDegree.BinaryLinear

namespace MIPRE.LowDegree.BinaryLinear
section
open Cost Cost.PolyTimeFun
/-- Executable matrix application agrees with the usual binary matrix-vector product. -/
theorem applyBits_matrixBits {m n : ℕ} (A : Matrix (Fin m) (Fin n) (ZMod 2))
    (v : Fin n → ZMod 2) :
    applyBits (matrixBits A) (vectorBits v) = vectorBits (A.mulVec v) := by
  simp only [applyBits, matrixBits, List.map_ofFn, vectorBits]
  apply congrArg List.ofFn
  funext i
  exact dotBits_vectorBits (A i) v
end
end MIPRE.LowDegree.BinaryLinear

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.LowDegree.BinaryLinear
open Cost Cost.PolyTimeFun
theorem _root_.solution {m n r : ℕ}
    (A : Matrix (Fin m) (Fin r) (ZMod 2)) (B : Matrix (Fin r) (Fin n) (ZMod 2)) :
    mulBits n (matrixBits A) (matrixBits B) = matrixBits (A * B) := by
  rw [mulBits, transposeBits_matrixBits]
  simp only [matrixBits, List.map_ofFn]
  apply congrArg List.ofFn
  funext i
  change applyBits (matrixBits B.transpose) (vectorBits (A i)) = vectorBits ((A * B) i)
  rw [applyBits_matrixBits]
  congr 1
  funext j
  simp only [Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.transpose_apply]
  apply Finset.sum_congr rfl
  intro k _
  exact mul_comm _ _
end MIPRE.LowDegree.BinaryLinear
