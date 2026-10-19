-- Prove2me | solution 1 for MIPRE.LowDegree.BinaryQuotient.fixedMatrix_ker
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T02:43:55.192419+00:00
-- url     : https://prove2.me/submissions/db110715-9581-4118-8fe0-7278b22b0000

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/LowDegree/BinaryQuotientFrobenius.lean (solution of MIPRE.LowDegree.BinaryQuotient.fixedMatrix_ker);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.CharP.Algebra
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
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.RingTheory.AdjoinRoot
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
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryQuotient
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
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryQuotientFrobenius

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.LowDegree.BinaryQuotient
open Cost BinaryPolynomial BinaryLinear
variable (f : Polynomial (ZMod 2)) (hf : f.Monic)
theorem _root_.solution (x : AdjoinRoot f) :
    coordinateEquiv f hf x ∈ (fixedMatrix f hf).mulVecLin.ker ↔ x * x = x := by
  rw [LinearMap.mem_ker]
  change (frobeniusMatrix f hf + 1).mulVec (coordinateEquiv f hf x) = 0 ↔ _
  rw [Matrix.add_mulVec, Matrix.one_mulVec]
  have hs : (frobeniusMatrix f hf).mulVec (coordinateEquiv f hf x) =
      coordinateEquiv f hf (x * x) := by
    simpa only [coordinateEquiv, frobeniusMatrix, Module.Basis.equivFun_apply,
      frobeniusLinear_apply, pow_two]
      using LinearMap.toMatrix_mulVec_repr (AdjoinRoot.powerBasisAux' hf)
        (AdjoinRoot.powerBasisAux' hf) (frobeniusLinear f) x
  rw [hs, ← map_add, ← (coordinateEquiv f hf).map_zero,
    (coordinateEquiv f hf).injective.eq_iff]
  by_cases ht : Nontrivial (AdjoinRoot f)
  · let : Nontrivial (AdjoinRoot f) := ht
    let : CharP (AdjoinRoot f) 2 :=
      charP_of_injective_ringHom (AdjoinRoot.of f).injective 2
    exact CharTwo.add_eq_zero
  · have : Subsingleton (AdjoinRoot f) := not_nontrivial_iff_subsingleton.mp ht
    exact ⟨fun _ => Subsingleton.elim _ _, fun _ => Subsingleton.elim _ _⟩
end MIPRE.LowDegree.BinaryQuotient
