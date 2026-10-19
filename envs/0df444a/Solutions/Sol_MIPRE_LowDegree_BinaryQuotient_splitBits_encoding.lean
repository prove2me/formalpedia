-- Prove2me | solution 1 for MIPRE.LowDegree.BinaryQuotient.splitBits_encoding
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T03:09:17.722805+00:00
-- url     : https://prove2.me/submissions/eff8b954-a833-4407-a7e7-f5c6e73936f5

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/LowDegree/BinaryQuotientComponents.lean (solution of MIPRE.LowDegree.BinaryQuotient.splitBits_encoding);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.Polynomial.Div
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
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryConstants
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryQuotient
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryNormalize
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryDivision
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
import Definitions.Def_MIPRE_Foundations_Cost_Iterates
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryCirculantProg
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryKernel
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryGroupAlgebra
import Definitions.Def_MIPRE_Foundations_LowDegree_FiniteReducedComponents
import Definitions.Def_MIPRE_Foundations_LowDegree_IdempotentSplit
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryComponents
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryComponentsProg
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryQuotientFrobenius
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryQuotientComponents
import Theorems.Thm_MIPRE_LowDegree_BinaryPolynomial_evalBits_mulReduce
import Theorems.Thm_MIPRE_LowDegree_BinaryPolynomial_evalBits_xor
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
/-- The fixed XOR program implements addition for any monic quotient. -/
theorem ofBits_xor (a b : BitStr)
    (ha : a.length = f.natDegree) (hb : b.length = f.natDegree) :
    ofBits f hf (xorBitsProg (a, b)) = ofBits f hf a + ofBits f hf b := by
  nontriviality (AdjoinRoot f)
  let : CharP (AdjoinRoot f) 2 :=
    charP_of_injective_ringHom (AdjoinRoot.of f).injective 2
  rw [xorBitsProg_apply, ofBits_eq_evalBits f hf _ (by simp [ha, hb]),
    ofBits_eq_evalBits f hf a ha, ofBits_eq_evalBits f hf b hb]
  exact evalBits_xor (AdjoinRoot.root f) a b (ha.trans hb.symm)
end
end MIPRE.LowDegree.BinaryQuotient

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

namespace MIPRE.LowDegree.BinaryQuotient
noncomputable section
open Cost Cost.PolyTimeFun Polynomial BinaryPolynomial
variable (f : Polynomial (ZMod 2)) (hf : f.Monic)
/-- Canonical encoding is injective for every monic quotient. -/
theorem toBits_injective : Function.Injective (toBits f hf) := by
  intro x y h
  have he := congrArg (ofBits f hf) h
  simpa only [ofBits_toBits] using he
end
end MIPRE.LowDegree.BinaryQuotient

namespace MIPRE.LowDegree.BinaryQuotient
noncomputable section
open Cost Cost.PolyTimeFun Polynomial BinaryPolynomial
variable (f : Polynomial (ZMod 2)) (hf : f.Monic)
/-- The zero row agrees with the canonical zero encoding. -/
theorem zeroRow_toBits (x : AdjoinRoot f) :
    BinaryLinear.zeroRow (toBits f hf x) = toBits f hf 0 := by
  simp only [BinaryLinear.zeroRow, toBits, List.map_ofFn, map_zero, Finsupp.zero_apply]
  rfl
end
end MIPRE.LowDegree.BinaryQuotient

namespace MIPRE.LowDegree.BinaryQuotient
noncomputable section
open Cost Cost.PolyTimeFun Polynomial BinaryPolynomial
variable (f : Polynomial (ZMod 2)) (hf : f.Monic)
/-- The raw zero test faithfully recognizes quotient zero on canonical encodings. -/
theorem nonzeroRow_toBits (x : AdjoinRoot f) :
    BinaryLinear.nonzeroRow (toBits f hf x) = decide (x ≠ 0) := by
  unfold BinaryLinear.nonzeroRow
  rw [zeroRow_toBits]
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  exact not_congr (toBits_injective f hf).eq_iff
end
end MIPRE.LowDegree.BinaryQuotient

namespace MIPRE.LowDegree.BinaryQuotient
noncomputable section
open Cost Cost.PolyTimeFun Polynomial BinaryPolynomial
variable (f : Polynomial (ZMod 2)) (hf : f.Monic)
/-- Raw XOR agrees exactly with canonical encoding of quotient addition. -/
theorem xorBits_toBits (x y : AdjoinRoot f) :
    xorBits (toBits f hf x) (toBits f hf y) = toBits f hf (x + y) := by
  have h := congrArg (toBits f hf)
    (ofBits_xor f hf (toBits f hf x) (toBits f hf y) (length_toBits f hf x) (length_toBits f hf y))
  have hw : (xorBits (toBits f hf x) (toBits f hf y)).length = f.natDegree := by
    rw [length_xorBits, length_toBits, length_toBits, min_self]
  simpa only [xorBitsProg_apply, toBits_ofBits f hf _ hw, ofBits_toBits] using h
end
end MIPRE.LowDegree.BinaryQuotient

namespace MIPRE.LowDegree.BinaryQuotient
noncomputable section
open Cost Cost.PolyTimeFun Polynomial BinaryPolynomial
variable (f : Polynomial (ZMod 2)) (hf : f.Monic)
/-- Raw modular multiplication agrees with canonical quotient multiplication. -/
theorem mulReduce_toBits (p : BitStr) (hp : p.length = f.natDegree)
    (hpoly : f = polyOfBits (p ++ [true])) (x y : AdjoinRoot f) :
    mulReduce p (toBits f hf x) (toBits f hf y) = toBits f hf (x * y) := by
  have h := congrArg (toBits f hf)
    (ofBits_mulReduce f hf p (toBits f hf x) (toBits f hf y) hp hpoly
      (length_toBits f hf x) (length_toBits f hf y))
  simpa only [mulReduceProg_apply, toBits_ofBits f hf _
    ((length_mulReduce _ _ _ ((length_toBits f hf x).trans hp.symm)).trans hp), ofBits_toBits] using h
end
end MIPRE.LowDegree.BinaryQuotient

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.LowDegree.BinaryQuotient
open Cost Cost.PolyTimeFun Polynomial BinaryPolynomial
variable (f : Polynomial (ZMod 2)) (hf : f.Monic)
theorem _root_.solution (p : BitStr) (hp : p.length = f.natDegree)
    (hpoly : f = polyOfBits (p ++ [true])) (e b : AdjoinRoot f) :
    splitBits p (toBits f hf e) (toBits f hf b) =
      (splitComponent e b).map (toBits f hf) := by
  unfold splitBits
  rw [mulReduce_toBits f hf p hp hpoly]
  dsimp only
  rw [xorBits_toBits]
  have he : e + e * b = e * (1 - b) := by
    nontriviality (AdjoinRoot f)
    let : CharP (AdjoinRoot f) 2 :=
      charP_of_injective_ringHom (AdjoinRoot.of f).injective 2
    rw [CharTwo.sub_eq_add, mul_add, mul_one]
  rw [he]
  unfold splitComponent
  by_cases h₁ : e * b = 0 <;> by_cases h₂ : e * (1 - b) = 0 <;>
    simp [nonzeroRow_toBits, h₁, h₂]
end MIPRE.LowDegree.BinaryQuotient
