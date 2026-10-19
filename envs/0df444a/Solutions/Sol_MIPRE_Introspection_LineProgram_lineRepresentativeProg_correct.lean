-- Prove2me | solution 1 for MIPRE.Introspection.LineProgram.lineRepresentativeProg_correct
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T05:55:28.860218+00:00
-- url     : https://prove2.me/submissions/a3e2371c-ebd8-45a2-a384-16e736dfa1d3

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/LineRepresentativeProg.lean (solution of MIPRE.Introspection.LineProgram.lineRepresentativeProg_correct);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Basic
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Rotate
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.FieldTheory.Finite.Trace
import Mathlib.FieldTheory.Galois.NormalBasis
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.KummerExtension
import Mathlib.FieldTheory.Minpoly.Finite
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Matrix.Circulant
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Pi
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.Polynomial.Content
import Mathlib.RingTheory.Polynomial.Cyclotomic.Factorization
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.Trace.Basic
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
import Definitions.Def_MIPRE_Foundations_SAT_Decoupled
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Fold
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_SAT_Pcp
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryRepresentation
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryPolynomial
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryConstants
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryPower
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
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryQuotientFactors
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryGCD
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryFactorization
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryCyclotomicSeed
import Definitions.Def_MIPRE_Foundations_LowDegree_BinarySubstitution
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryNonresidueLoop
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryNonresidueCorrectness
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryQuotientOrbit
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryTraceBits
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryOrbitPolynomial
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryOrbitDescent
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryQuotientPolynomial
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryQuotientTranslation
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryCoprimeDegree
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryComposedSumPolynomial
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryComposedSumProg
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryOddPrimeProgram
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryPrimePowerTrace
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryArtinSchreier
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryArtinSchreierProg
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryArtinSchreierTower
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryArtinSchreierLoop
import Definitions.Def_MIPRE_Foundations_LowDegree_UnaryDegreeArithmetic
import Definitions.Def_MIPRE_Foundations_LowDegree_UnaryPrimality
import Definitions.Def_MIPRE_Foundations_LowDegree_UnaryPrimePower
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryDegreeFactors
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryDegreeDecomposition
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryPrimePowerDispatch
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryIrreducibleAssembly
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryIrreducibleConstructor
import Definitions.Def_MIPRE_Foundations_LowDegree_Shoup
import Definitions.Def_MIPRE_Foundations_LowDegree_ShoupCoefficients
import Definitions.Def_MIPRE_Foundations_SAT_QuotientField
import Definitions.Def_MIPRE_Foundations_SAT_FieldTrace
import Definitions.Def_MIPRE_Foundations_SAT_FieldCoordinates
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryFold
import Definitions.Def_MIPRE_Foundations_SAT_NormalElementProg
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryInverse
import Definitions.Def_MIPRE_Foundations_Introspection_LineRepresentativeProg
import Theorems.Thm_MIPRE_LowDegree_BinaryLinear_xorBits_vectorBits
import Theorems.Thm_MIPRE_SAT_shoupBinField_charP
import Theorems.Thm_MIPRE_SAT_shoupInvProg_correct
import Theorems.Thm_MIPRE_SAT_shoupMulProg_encoding

attribute [instance] MIPRE.SAT.shoupBinField_charP

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.LowDegree.BinaryLinear
noncomputable section
open Cost
attribute [local instance] MIPRE.LowDegree.BinaryLinear.instFactPrimeOfNatNat_mIPRE_2
theorem vectorBits_injective {k : ℕ} : Function.Injective (vectorBits (n := k)) := by
  intro v w h
  have he := congrArg (vectorValue k) h
  simpa using he
end
end MIPRE.LowDegree.BinaryLinear

namespace MIPRE.SAT
noncomputable section
open Cost LowDegree LowDegree.BinaryPolynomial LowDegree.BinaryLinear
attribute [local instance] MIPRE.SAT.instFactPrimeOfNatNat_mIPRE_1
/-- Canonical field encodings and canonical linear coordinates coincide exactly. -/
theorem shoupCoordinateEquiv_encoding (k : ℕ) (hk : 1 ≤ k)
    (a : (shoupBinField k hk).carrier) :
    vectorBits (shoupCoordinateEquiv k hk a) = (shoupBinField k hk).toBits a :=
  vectorBits_vectorValue k _ ((shoupBinField k hk).length_toBits a)
end
end MIPRE.SAT

namespace MIPRE.SAT
noncomputable section
open Cost Cost.PolyTimeFun LowDegree LowDegree.BinaryLinear Polynomial
local instance instFactPrimeOfNatNat_mIPRE_6 : Fact (Nat.Prime 2) := ⟨by decide⟩
end
end MIPRE.SAT

namespace MIPRE.SAT
noncomputable section
open Cost Cost.PolyTimeFun LowDegree LowDegree.BinaryLinear Polynomial
attribute [local instance] MIPRE.SAT.instFactPrimeOfNatNat_mIPRE_6
theorem shoupZeroProg_correct (k : ℕ) (hk : 1 ≤ k) :
    shoupZeroProg (unary k) = (shoupBinField k hk).toBits 0 := by
  rw [← shoupCoordinateEquiv_encoding, map_zero]
  change (unary k).map (fun _ => false) = vectorBits (0 : Fin k → ZMod 2)
  apply List.ext_getElem
  · simp [vectorBits]
  · intro i hi hj
    simp [vectorBits, bit]
end
end MIPRE.SAT

namespace MIPRE.SAT
noncomputable section
open Cost Cost.PolyTimeFun LowDegree LowDegree.BinaryLinear Polynomial
attribute [local instance] MIPRE.SAT.instFactPrimeOfNatNat_mIPRE_6
theorem shoupNonzeroRow_correct (k : ℕ) (hk : 1 ≤ k) (a : (shoupBinField k hk).carrier) :
    nonzeroRow ((shoupBinField k hk).toBits a) = decide (a ≠ 0) := by
  rw [← shoupCoordinateEquiv_encoding]
  unfold nonzeroRow
  rw [zeroRow_vectorBits, ← (shoupCoordinateEquiv k hk).map_zero]
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  exact not_congr ((vectorBits_injective (k := k)).eq_iff.trans
    (shoupCoordinateEquiv k hk).injective.eq_iff)
end
end MIPRE.SAT

namespace MIPRE.SAT
noncomputable section
open Cost Cost.PolyTimeFun LowDegree LowDegree.BinaryLinear Polynomial
attribute [local instance] MIPRE.SAT.instFactPrimeOfNatNat_mIPRE_6
theorem shoupXorBits_correct (k : ℕ) (hk : 1 ≤ k) (a b : (shoupBinField k hk).carrier) :
    BinaryPolynomial.xorBits ((shoupBinField k hk).toBits a) ((shoupBinField k hk).toBits b) =
      (shoupBinField k hk).toBits (a + b) := by
  simp only [← shoupCoordinateEquiv_encoding, xorBits_vectorBits, map_add]
end
end MIPRE.SAT

namespace MIPRE.Introspection.LineProgram
noncomputable section
open Cost Cost.PolyTimeFun Polynomial LowDegree LowDegree.BinaryLinear SAT
theorem firstPairBitsProg_correct (k : ℕ) (hk : 1 ≤ k)
    (l : List ((shoupBinField k hk).carrier × (shoupBinField k hk).carrier)) :
    firstPairBitsProg
      (l.map (fun p => ((shoupBinField k hk).toBits p.1, (shoupBinField k hk).toBits p.2)),
        ((shoupBinField k hk).toBits 0, (shoupBinField k hk).toBits 0)) =
      ((shoupBinField k hk).toBits (firstPair l).1,
        (shoupBinField k hk).toBits (firstPair l).2) := by
  change (l.map _).foldr _ _ = _
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.map_cons, List.foldr_cons, shoupNonzeroRow_correct, ih]
    by_cases ha : a.2 = 0 <;> simp [firstPair, ha]
end
end MIPRE.Introspection.LineProgram

namespace MIPRE.Introspection.LineProgram
noncomputable section
open Cost Cost.PolyTimeFun Polynomial LowDegree LowDegree.BinaryLinear SAT
theorem coefficientOfPairProg_correct (k : ℕ) (hk : 1 ≤ k)
    (a c : (shoupBinField k hk).carrier) :
    coefficientOfPairProg (unary k, (shoupBinField k hk).toBits a,
      (shoupBinField k hk).toBits c) =
      (shoupBinField k hk).toBits (if c ≠ 0 then a * c⁻¹ else 0) := by
  change (if nonzeroRow ((shoupBinField k hk).toBits c) then
    shoupMulProg (unary k, (shoupBinField k hk).toBits a,
      shoupInvProg (unary k, (shoupBinField k hk).toBits c)) else
    shoupZeroProg (unary k)) = _
  rw [shoupNonzeroRow_correct]
  by_cases hc : c = 0
  · simp only [hc, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, if_false]
    exact shoupZeroProg_correct k hk
  · simp only [hc, ne_eq, not_false_eq_true, decide_true, if_true]
    rw [shoupInvProg_correct k hk c hc, shoupMulProg_encoding]
end
end MIPRE.Introspection.LineProgram

namespace MIPRE.Introspection.LineProgram
noncomputable section
open Cost Cost.PolyTimeFun Polynomial LowDegree LowDegree.BinaryLinear SAT
theorem coefficientBitsProg_correct (k : ℕ) (hk : 1 ≤ k)
    (l : List ((shoupBinField k hk).carrier × (shoupBinField k hk).carrier)) :
    coefficientBitsProg
      (unary k, l.map (fun p => ((shoupBinField k hk).toBits p.1,
        (shoupBinField k hk).toBits p.2))) =
      (shoupBinField k hk).toBits (coefficient l) := by
  change coefficientOfPairProg (unary k, firstPairBitsProg
    (l.map _, (shoupZeroProg (unary k), shoupZeroProg (unary k)))) = _
  rw [shoupZeroProg_correct k hk, firstPairBitsProg_correct,
    coefficientOfPairProg_correct]
  rfl
end
end MIPRE.Introspection.LineProgram

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Introspection.LineProgram
open Cost Cost.PolyTimeFun Polynomial LowDegree LowDegree.BinaryLinear SAT
theorem _root_.solution (k : ℕ) (hk : 1 ≤ k) {n : ℕ}
    (u v : Fin n → (shoupBinField k hk).carrier) :
    lineRepresentativeProg (unary k, (shoupBinField k hk).vecBits u,
      (shoupBinField k hk).vecBits v) =
      (shoupBinField k hk).vecBits (representative u v) := by
  let l := List.ofFn fun i => (u i, v i)
  have hz : ((shoupBinField k hk).vecBits u).zip ((shoupBinField k hk).vecBits v) =
      l.map (fun p => ((shoupBinField k hk).toBits p.1,
        (shoupBinField k hk).toBits p.2)) := by
    apply List.ext_getElem
    · simp [BinField.vecBits, l]
    · intro i hi hj
      simp [BinField.vecBits, l]
  change (((shoupBinField k hk).vecBits u).zip ((shoupBinField k hk).vecBits v)).map
    (fun p => BinaryPolynomial.xorBits p.1
      (shoupMulProg (unary k, coefficientBitsProg (unary k,
        ((shoupBinField k hk).vecBits u).zip ((shoupBinField k hk).vecBits v)), p.2))) = _
  rw [hz, coefficientBitsProg_correct]
  simp only [l, List.map_ofFn, BinField.vecBits]
  apply congrArg List.ofFn
  funext i
  change BinaryPolynomial.xorBits ((shoupBinField k hk).toBits (u i))
    (shoupMulProg (unary k, (shoupBinField k hk).toBits (coefficient l),
      (shoupBinField k hk).toBits (v i))) =
    (shoupBinField k hk).toBits (u i - coefficient l * v i)
  rw [shoupMulProg_encoding, shoupXorBits_correct, CharTwo.sub_eq_add]
end MIPRE.Introspection.LineProgram
