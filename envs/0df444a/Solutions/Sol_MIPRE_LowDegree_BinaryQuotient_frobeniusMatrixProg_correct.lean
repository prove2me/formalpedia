-- Prove2me | solution 1 for MIPRE.LowDegree.BinaryQuotient.frobeniusMatrixProg_correct
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T02:43:54.675983+00:00
-- url     : https://prove2.me/submissions/d8c1dc3f-8e24-42b7-8ab7-d18631aadc4e

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/LowDegree/BinaryQuotientFrobenius.lean (solution of MIPRE.LowDegree.BinaryQuotient.frobeniusMatrixProg_correct);
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
import Theorems.Thm_MIPRE_LowDegree_BinaryLinear_transposeBits_matrixBits
import Theorems.Thm_MIPRE_LowDegree_BinaryPolynomial_evalBits_mulReduce
import Theorems.Thm_MIPRE_LowDegree_BinaryPolynomial_length_mulReduce
import Theorems.Thm_MIPRE_LowDegree_BinaryQuotient_root_eq
import Theorems.Thm_MIPRE_LowDegree_BinaryQuotient_toBits_ofBits

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.LowDegree.BinaryQuotient
noncomputable section
open Cost BinaryPolynomial
variable (f : Polynomial (ZMod 2)) (hf : f.Monic)
/-- Uniform modular multiplication works before irreducibility is known. -/
theorem ofBits_mulReduce (p a b : BitStr)
    (hp : p.length = f.natDegree) (hpoly : f = polyOfBits (p ++ [true]))
    (ha : a.length = f.natDegree) (hb : b.length = f.natDegree) :
    ofBits f hf (mulReduceProg (p, a, b)) = ofBits f hf a * ofBits f hf b := by
  nontriviality (AdjoinRoot f)
  let : CharP (AdjoinRoot f) 2 :=
    charP_of_injective_ringHom (AdjoinRoot.of f).injective 2
  rw [mulReduceProg_apply, ofBits_eq_evalBits f hf _
      ((length_mulReduce p a b (ha.trans hp.symm)).trans hp),
    ofBits_eq_evalBits f hf a ha, ofBits_eq_evalBits f hf b hb]
  exact evalBits_mulReduce _ p a b (ha.trans hp.symm) (root_eq f p hpoly)
end
end MIPRE.LowDegree.BinaryQuotient

namespace MIPRE.LowDegree.BinaryLinear
section
open Cost Cost.PolyTimeFun
theorem unitBits_eq_vectorBits {n : ℕ} (j : Fin n) :
    unitBits n j = vectorBits (Pi.single j 1 : Fin n → ZMod 2) := by
  apply List.ext_getElem
  · simp [unitBits, vectorBits]
  · intro i hi hj
    simp only [unitBits, vectorBits, List.getElem_map, List.getElem_range, List.getElem_ofFn]
    by_cases he : i = j
    · simp [bit, Pi.single_apply, Fin.ext_iff, he]
    · simp [bit, Pi.single_apply, Fin.ext_iff, he]
end
end MIPRE.LowDegree.BinaryLinear

namespace MIPRE.LowDegree.BinaryQuotient
noncomputable section
open Cost BinaryPolynomial BinaryLinear
variable (f : Polynomial (ZMod 2)) (hf : f.Monic)
/-- Quotient bit encodings agree with the generic binary linear coordinates. -/
theorem toBits_eq_vectorBits (x : AdjoinRoot f) :
    toBits f hf x = vectorBits (coordinateEquiv f hf x) := rfl
end
end MIPRE.LowDegree.BinaryQuotient

namespace MIPRE.LowDegree.BinaryQuotient
noncomputable section
open Cost BinaryPolynomial BinaryLinear
variable (f : Polynomial (ZMod 2)) (hf : f.Monic)
/-- A power-basis vector has the corresponding standard unit-vector encoding. -/
theorem toBits_basis (j : Fin f.natDegree) :
    toBits f hf ((AdjoinRoot.powerBasisAux' hf) j) = unitBits f.natDegree j := by
  rw [toBits_eq_vectorBits, unitBits_eq_vectorBits]
  congr 1
  ext i
  by_cases h : j = i <;> simp [coordinateEquiv, h]
end
end MIPRE.LowDegree.BinaryQuotient

namespace MIPRE.LowDegree.BinaryQuotient
noncomputable section
open Cost BinaryPolynomial BinaryLinear
variable (f : Polynomial (ZMod 2)) (hf : f.Monic)
/-- The supplied-modulus squaring program prints the canonical quotient encoding. -/
theorem squareProg_correct (p : BitStr)
    (hp : p.length = f.natDegree) (hpoly : f = polyOfBits (p ++ [true]))
    (x : AdjoinRoot f) :
    squareProg (p, toBits f hf x) = toBits f hf (frobeniusLinear f x) := by
  have h := ofBits_mulReduce f hf p (toBits f hf x) (toBits f hf x) hp hpoly
    (length_toBits f hf x) (length_toBits f hf x)
  have hw : (mulReduceProg (p, toBits f hf x, toBits f hf x)).length = f.natDegree := by
    rw [mulReduceProg_apply, length_mulReduce p _ _ ((length_toBits f hf x).trans hp.symm), hp]
  have he := congrArg (toBits f hf) h
  rw [toBits_ofBits f hf _ hw, ofBits_toBits] at he
  simpa only [squareProg, Cost.PolyTimeFun.comp_apply, Cost.PolyTimeFun.pair_apply,
    Cost.PolyTimeFun.fst_apply, Cost.PolyTimeFun.snd_apply,
    frobeniusLinear_apply, pow_two] using he
end
end MIPRE.LowDegree.BinaryQuotient

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.LowDegree.BinaryQuotient
open Cost BinaryPolynomial BinaryLinear
variable (f : Polynomial (ZMod 2)) (hf : f.Monic)
theorem _root_.solution (p : BitStr)
    (hp : p.length = f.natDegree) (hpoly : f = polyOfBits (p ++ [true])) :
    frobeniusMatrixProg p = matrixBits (frobeniusMatrix f hf) := by
  let A := frobeniusMatrix f hf
  have hc : (identityBits f.natDegree).map (fun v => squareProg (p, v)) =
      matrixBits A.transpose := by
    apply List.ext_getElem
    · simp [identityBits, matrixBits]
    · intro j hj hj'
      have hjk : j < f.natDegree := by simpa [identityBits] using hj
      simp only [identityBits, List.getElem_map, List.getElem_range, matrixBits,
        List.getElem_ofFn]
      rw [← toBits_basis f hf (⟨j, hjk⟩ : Fin f.natDegree),
        squareProg_correct f hf p hp hpoly, toBits_eq_vectorBits]
      congr 1
      funext i
      exact (LinearMap.toMatrix_apply (AdjoinRoot.powerBasisAux' hf)
        (AdjoinRoot.powerBasisAux' hf) (frobeniusLinear f) i ⟨j, hjk⟩).symm
  simp only [frobeniusMatrixProg, Cost.PolyTimeFun.comp_apply,
    Cost.PolyTimeFun.pair_apply, Cost.PolyTimeFun.id_apply,
    Cost.PolyTimeFun.mapWith_apply, Cost.PolyTimeFun.fst_apply,
    Cost.PolyTimeFun.snd_apply, Cost.PolyTimeFun.length_apply]
  change transposeBits (unary p.length).length
    ((identityBits (unary p.length).length).map (fun v => squareProg (p, v))) = _
  rw [length_unary, hp, hc, transposeBits_matrixBits, Matrix.transpose_transpose]
end MIPRE.LowDegree.BinaryQuotient
