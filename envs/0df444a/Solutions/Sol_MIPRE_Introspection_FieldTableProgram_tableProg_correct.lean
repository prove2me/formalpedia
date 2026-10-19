-- Prove2me | solution 1 for MIPRE.Introspection.FieldTableProgram.tableProg_correct
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T06:28:06.178689+00:00
-- url     : https://prove2.me/submissions/2735f386-0b5f-4a14-8845-0322bc061bc3

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/FieldTableProg.lean (solution of MIPRE.Introspection.FieldTableProgram.tableProg_correct);
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
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.Polynomial.Roots
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
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.FieldTheory.Finite.GaloisField
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
import Definitions.Def_MIPRE_Foundations_LowDegree_SchwartzZippel
import Definitions.Def_MIPRE_Foundations_LowDegree_Anticomm
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryRepresentation
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryPolynomial
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryConstants
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryPower
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryTrace
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
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryKernel
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryGroupAlgebra
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryGroupAlgebra_B
import Definitions.Def_MIPRE_Foundations_LowDegree_FiniteReducedComponents
import Definitions.Def_MIPRE_Foundations_LowDegree_IdempotentSplit
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryComponents
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryComponents_B
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryComponentsProg
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryComponentsProg_B
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
import Definitions.Def_MIPRE_Foundations_SAT_FieldTrace_B
import Definitions.Def_MIPRE_Foundations_SAT_FieldCoordinates
import Definitions.Def_MIPRE_Foundations_SAT_TraceGram
import Definitions.Def_MIPRE_Foundations_LowDegree_SelfDual
import Definitions.Def_MIPRE_Foundations_LowDegree_NormalBasis
import Definitions.Def_MIPRE_Foundations_SAT_NormalGram
import Definitions.Def_MIPRE_Foundations_SAT_FrobeniusAction
import Definitions.Def_MIPRE_Foundations_SAT_NormalElement
import Definitions.Def_MIPRE_Foundations_SAT_FrobeniusMatrix
import Definitions.Def_MIPRE_Foundations_SAT_FrobeniusActionProg
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryFold
import Definitions.Def_MIPRE_Foundations_SAT_NormalElementProg
import Definitions.Def_MIPRE_Foundations_SAT_NormalElementProg_B
import Definitions.Def_MIPRE_Foundations_Introspection_FieldIndicatorProg
import Definitions.Def_MIPRE_Foundations_Introspection_FieldTableProg
import Theorems.Thm_MIPRE_LowDegree_BinaryLinear_xorBits_vectorBits
import Theorems.Thm_MIPRE_LowDegree_BinaryPolynomial_evalBits_oneBits
import Theorems.Thm_MIPRE_SAT_bitsVal_injective
import Theorems.Thm_MIPRE_SAT_shoupBinField_charP
import Theorems.Thm_MIPRE_SAT_shoupMulProg_encoding
import Theorems.Thm_MIPRE_SAT_shoupRoot_eval_eq_iff
import Theorems.Thm_MIPRE_SAT_shoupRoot_eval_toBits

attribute [instance] MIPRE.SAT.shoupBinField_charP

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.LowDegree
noncomputable section
open Finset MvPolynomial
variable {K : Type*} [CommRing K] {m : ℕ}
theorem indVec_apply (x : Fin m → K) (y : Fin m → Bool) :
    indVec x y = ∏ i, if y i then x i else 1 - x i := by
  rw [indVec, ind, map_prod]
  exact Finset.prod_congr rfl fun i _ => by cases y i <;> simp
end
end MIPRE.LowDegree

namespace MIPRE.SAT
section
open Cost
theorem bitsVal_cons' (b : Bool) (l : BitStr) : bitsVal (b :: l) = 2 * bitsVal l + b.toNat := by
  rw [bitsVal_cons]; cases b <;> simp [Nat.bit]
end
end MIPRE.SAT

namespace MIPRE.SAT
section
open Cost
theorem bitsVal_append (l₁ l₂ : BitStr) :
    bitsVal (l₁ ++ l₂) = bitsVal l₁ + 2 ^ l₁.length * bitsVal l₂ := by
  induction l₁ with
  | nil => simp [bitsVal_nil]
  | cons b l ih =>
    rw [List.cons_append, bitsVal_cons', bitsVal_cons', ih, List.length_cons, Nat.pow_succ]; ring
end
end MIPRE.SAT

namespace MIPRE.SAT
section
open Cost
theorem bitsVal_replicate_false (n : ℕ) : bitsVal (List.replicate n false) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [List.replicate_succ, bitsVal_cons', ih]; rfl
end
end MIPRE.SAT

namespace MIPRE.SAT
section
open Cost
theorem length_padBits (W : ℕ) (l : BitStr) (h : l.length ≤ W) : (padBits W l).length = W := by
  simp [padBits]; omega
end
end MIPRE.SAT

namespace MIPRE.SAT
section
open Cost
theorem bitsVal_padBits (W : ℕ) (l : BitStr) : bitsVal (padBits W l) = bitsVal l := by
  rw [padBits, bitsVal_append, bitsVal_replicate_false]; ring
end
end MIPRE.SAT

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
open Cost LowDegree LowDegree.BinaryLinear LowDegree.BinaryPolynomial
attribute [local instance] MIPRE.SAT.instFactPrimeOfNatNat_mIPRE_2
/-- The actual coefficient-vector representation of the unit. -/
theorem shoupBinField_oneBits (k : ℕ) (hk : 1 ≤ k) (v : BitStr) (hv : v.length = k) :
    BinaryPolynomial.oneBits v = (shoupBinField k hk).toBits 1 := by
  apply (shoupRoot_eval_eq_iff k hk _ _ (by simpa using hv)
    ((shoupBinField k hk).length_toBits _)).mp
  rw [shoupRoot_eval_toBits, BinaryPolynomial.evalBits_oneBits]
  intro he
  simp only [he, List.length_nil] at hv
  omega
end
end MIPRE.SAT

namespace MIPRE.LowDegree.BinaryPolynomial
section
open Cost Cost.PolyTimeFun Polynomial
theorem arithmeticFold_cons (mul : Bool) (p a b : BitStr) (l : List BitStr) :
    arithmeticFold mul p a (b :: l) =
      arithmeticFold mul p (if mul then mulReduce p a b else xorBits a b) l := rfl
end
end MIPRE.LowDegree.BinaryPolynomial

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
theorem shoupXorBits_correct (k : ℕ) (hk : 1 ≤ k) (a b : (shoupBinField k hk).carrier) :
    BinaryPolynomial.xorBits ((shoupBinField k hk).toBits a) ((shoupBinField k hk).toBits b) =
      (shoupBinField k hk).toBits (a + b) := by
  simp only [← shoupCoordinateEquiv_encoding, xorBits_vectorBits, map_add]
end
end MIPRE.SAT

namespace MIPRE.SAT
noncomputable section
open Cost Cost.PolyTimeFun LowDegree LowDegree.BinaryLinear Polynomial
attribute [local instance] MIPRE.SAT.instFactPrimeOfNatNat_mIPRE_6
theorem shoupArithmeticFold_add_correct (k : ℕ) (hk : 1 ≤ k)
    (l : List (shoupBinField k hk).carrier) (a : (shoupBinField k hk).carrier) (p : BitStr) :
    BinaryPolynomial.arithmeticFold false p ((shoupBinField k hk).toBits a)
      (l.map (shoupBinField k hk).toBits) = (shoupBinField k hk).toBits (a + l.sum) := by
  induction l generalizing a with
  | nil => simp [BinaryPolynomial.arithmeticFold]
  | cons b l ih =>
    rw [List.map_cons, BinaryPolynomial.arithmeticFold_cons]
    simp only [Bool.false_eq_true, if_false]
    rw [shoupXorBits_correct, ih, List.sum_cons, add_assoc]
end
end MIPRE.SAT

namespace MIPRE.SAT
noncomputable section
open Cost Cost.PolyTimeFun LowDegree LowDegree.BinaryLinear Polynomial
attribute [local instance] MIPRE.SAT.instFactPrimeOfNatNat_mIPRE_6
theorem shoupSumProg_correct (k : ℕ) (hk : 1 ≤ k) (l : List (shoupBinField k hk).carrier) :
    shoupSumProg (unary k, l.map (shoupBinField k hk).toBits) =
      (shoupBinField k hk).toBits l.sum := by
  change BinaryPolynomial.arithmeticFold false (shoupZeroProg (unary k))
    (shoupZeroProg (unary k)) (l.map (shoupBinField k hk).toBits) = _
  rw [shoupZeroProg_correct k hk, shoupArithmeticFold_add_correct, zero_add]
end
end MIPRE.SAT

namespace MIPRE.Introspection.FieldIndicatorProgram
noncomputable section
open Cost Cost.PolyTimeFun LowDegree LowDegree.BinaryPolynomial SAT
/-- Modular multiplication of canonical field rows computes their product. -/
theorem shoupArithmeticFold_mul_correct (k : ℕ) (hk : 1 ≤ k)
    (values : List (shoupBinField k hk).carrier) (a : (shoupBinField k hk).carrier) :
    arithmeticFold true (shoupLowerCoeffs (unary k)) ((shoupBinField k hk).toBits a)
      (values.map (shoupBinField k hk).toBits) =
      (shoupBinField k hk).toBits (a * values.prod) := by
  induction values generalizing a with
  | nil => simp [arithmeticFold]
  | cons b values ih =>
    rw [List.map_cons, arithmeticFold_cons]
    change arithmeticFold true (shoupLowerCoeffs (unary k))
      (shoupMulProg (unary k, (shoupBinField k hk).toBits a, (shoupBinField k hk).toBits b))
      (values.map (shoupBinField k hk).toBits) = _
    rw [shoupMulProg_encoding, ih, List.prod_cons, mul_assoc]
end
end MIPRE.Introspection.FieldIndicatorProgram

namespace MIPRE.Introspection.FieldIndicatorProgram
noncomputable section
open Cost Cost.PolyTimeFun LowDegree LowDegree.BinaryPolynomial SAT
theorem factorProg_correct (k : ℕ) (hk : 1 ≤ k)
    (x : (shoupBinField k hk).carrier) (b : Bool) :
    factorProg ((shoupBinField k hk).toBits x, b) =
      (shoupBinField k hk).toBits (if b then x else 1 - x) := by
  cases b with
  | true => rfl
  | false =>
    change xorBits (oneBits ((shoupBinField k hk).toBits x))
      ((shoupBinField k hk).toBits x) = _
    rw [shoupBinField_oneBits k hk _ ((shoupBinField k hk).length_toBits x),
      shoupXorBits_correct, CharTwo.sub_eq_add]
    rfl
end
end MIPRE.Introspection.FieldIndicatorProgram

namespace MIPRE.Introspection.FieldIndicatorProgram
noncomputable section
open Cost Cost.PolyTimeFun LowDegree LowDegree.BinaryPolynomial SAT
theorem indicatorProg_correct (k : ℕ) (hk : 1 ≤ k)
    (coords : List ((shoupBinField k hk).carrier × Bool)) :
    indicatorProg (unary k, coords.map (fun p => ((shoupBinField k hk).toBits p.1, p.2))) =
      (shoupBinField k hk).toBits ((coords.map (fun p => if p.2 then p.1 else 1 - p.1)).prod) := by
  have hmap :
      (coords.map (fun p => ((shoupBinField k hk).toBits p.1, p.2))).map factorProg =
      (coords.map (fun p => if p.2 then p.1 else 1 - p.1)).map (shoupBinField k hk).toBits := by
    simp only [List.map_map]
    apply List.map_congr_left
    intro p _
    exact factorProg_correct k hk p.1 p.2
  change arithmeticFold true (shoupLowerCoeffs (unary k))
    (oneBits (shoupZeroProg (unary k)))
    ((coords.map (fun p => ((shoupBinField k hk).toBits p.1, p.2))).map factorProg) = _
  rw [hmap, shoupZeroProg_correct k hk,
    shoupBinField_oneBits k hk _ ((shoupBinField k hk).length_toBits 0),
    shoupArithmeticFold_mul_correct, one_mul]
end
end MIPRE.Introspection.FieldIndicatorProgram

namespace MIPRE.Introspection.FieldIndicatorProgram
noncomputable section
open Cost Cost.PolyTimeFun LowDegree LowDegree.BinaryPolynomial SAT
/-- Exact indicator semantics at an arbitrary field point, not only on the cube. -/
theorem indicatorProg_indVec (k : ℕ) (hk : 1 ≤ k) {m : ℕ}
    (x : Fin m → (shoupBinField k hk).carrier) (y : Fin m → Bool) :
    indicatorProg (unary k, List.ofFn (fun i => ((shoupBinField k hk).toBits (x i), y i))) =
      (shoupBinField k hk).toBits (indVec x y) := by
  have h := indicatorProg_correct k hk (List.ofFn fun i => (x i, y i))
  simpa only [List.map_ofFn, List.prod_ofFn, indVec_apply, Function.comp_def] using h
end
end MIPRE.Introspection.FieldIndicatorProgram

namespace MIPRE.Introspection.FieldTableProgram
noncomputable section
open Cost Cost.PolyTimeFun SAT LowDegree FieldIndicatorProgram
theorem cubeEnumeration_bits {m : ℕ} (y : Fin m → Bool) :
    padBits m (cubeEnumeration m y).val.bits = List.ofFn y := by
  apply bitsVal_injective
  · rw [length_padBits, List.length_ofFn]
    rw [Nat.size_eq_bits_len]
    exact Nat.size_le.mpr (cubeEnumeration m y).isLt
  · rw [bitsVal_padBits, bitsVal_bits]
    rfl
end
end MIPRE.Introspection.FieldTableProgram

namespace MIPRE.Introspection.FieldTableProgram
noncomputable section
open Cost Cost.PolyTimeFun SAT LowDegree FieldIndicatorProgram
theorem cubeEnumeration_symm_bits {m : ℕ} (i : Fin (2 ^ m)) :
    padBits m i.val.bits = List.ofFn (cubeEnumeration m |>.symm i) := by
  simpa using cubeEnumeration_bits ((cubeEnumeration m).symm i)
end
end MIPRE.Introspection.FieldTableProgram

namespace MIPRE.Introspection.FieldTableProgram
noncomputable section
open Cost Cost.PolyTimeFun SAT LowDegree FieldIndicatorProgram
theorem termProg_correct (k : ℕ) (hk : 1 ≤ k) {m : ℕ}
    (x : Fin m → (shoupBinField k hk).carrier)
    (a : (shoupBinField k hk).carrier) (i : Fin (2 ^ m)) :
    termProg (((shoupBinField k hk).toBits a, i.val),
      (unary k, List.ofFn fun j => (shoupBinField k hk).toBits (x j))) =
      (shoupBinField k hk).toBits (a * indVec x ((cubeEnumeration m).symm i)) := by
  have hzip :
      (List.ofFn fun j => (shoupBinField k hk).toBits (x j)).zip
        (List.ofFn ((cubeEnumeration m).symm i)) =
      List.ofFn (fun j => ((shoupBinField k hk).toBits (x j),
        (cubeEnumeration m).symm i j)) := by
    apply List.ext_getElem
    · simp
    · intro j h₁ h₂
      simp
  simp only [termProg, comp_apply, pair_apply, fst_apply, snd_apply,
    length_apply, natBits_apply, padP_apply, zip_apply, length_unary, List.length_ofFn]
  rw [cubeEnumeration_symm_bits, hzip, indicatorProg_indVec, shoupMulProg_encoding]
end
end MIPRE.Introspection.FieldTableProgram

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Introspection.FieldTableProgram
open Cost Cost.PolyTimeFun SAT LowDegree FieldIndicatorProgram
theorem _root_.solution (k : ℕ) (hk : 1 ≤ k) {m : ℕ}
    (x : Fin m → (shoupBinField k hk).carrier)
    (h : (Fin m → Bool) → (shoupBinField k hk).carrier) :
    tableProg (unary k, List.ofFn (fun j => (shoupBinField k hk).toBits (x j)),
      List.ofFn (fun i : Fin (2 ^ m) =>
        (shoupBinField k hk).toBits (h ((cubeEnumeration m).symm i)))) =
      (shoupBinField k hk).toBits (MvPolynomial.eval x (ldEnc h)) := by
  classical
  have hzip :
      (List.ofFn fun i : Fin (2 ^ m) =>
        (shoupBinField k hk).toBits (h ((cubeEnumeration m).symm i))).zip
        (List.range' 0 (2 ^ m)) =
      List.ofFn (fun i : Fin (2 ^ m) =>
        ((shoupBinField k hk).toBits (h ((cubeEnumeration m).symm i)), i.val)) := by
    apply List.ext_getElem
    · simp
    · intro j h₁ h₂
      simp
  simp only [tableProg, comp_apply, pair_apply, fst_apply, snd_apply,
    range'P_apply, length_apply, length_unary, List.length_ofFn, zip_apply,
    mapWith_apply, const_apply, hzip, List.map_ofFn, Function.comp_def]
  simp only [termProg_correct]
  have hsum := shoupSumProg_correct k hk
    (List.ofFn fun i : Fin (2 ^ m) =>
      h ((cubeEnumeration m).symm i) * indVec x ((cubeEnumeration m).symm i))
  simp only [List.map_ofFn, Function.comp_def, List.sum_ofFn] at hsum
  rw [hsum]
  congr 1
  rw [ldEnc, map_sum]
  simp only [map_mul, MvPolynomial.eval_C]
  exact (Equiv.sum_comp (cubeEnumeration m).symm
    (fun y => h y * indVec x y))
end MIPRE.Introspection.FieldTableProgram
