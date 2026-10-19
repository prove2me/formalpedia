-- Prove2me | solution 1 for MIPRE.SAT.shoupTraceProg_correct
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T05:39:30.819087+00:00
-- url     : https://prove2.me/submissions/9aa3ec07-4382-447d-a90e-cdb55c165875

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/SAT/FieldTrace.lean (solution of MIPRE.SAT.shoupTraceProg_correct);
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
import Theorems.Thm_MIPRE_LowDegree_BinaryPolynomial_evalBits_mulReduce
import Theorems.Thm_MIPRE_LowDegree_BinaryPolynomial_evalBits_xor
import Theorems.Thm_MIPRE_LowDegree_BinaryPolynomial_length_mulReduce
import Theorems.Thm_MIPRE_LowDegree_shoupIrreducible_monic
import Theorems.Thm_MIPRE_LowDegree_shoupIrreducible_natDegree
import Theorems.Thm_MIPRE_SAT_shoupBinField_charP
import Theorems.Thm_MIPRE_SAT_shoupBinField_finrank
import Theorems.Thm_MIPRE_SAT_shoupRoot_equation
import Theorems.Thm_MIPRE_SAT_shoupRoot_eval_eq_iff
import Theorems.Thm_MIPRE_SAT_shoupRoot_eval_toBits

attribute [instance] MIPRE.SAT.shoupBinField_charP

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.LowDegree.BinaryPolynomial
section
open Cost
/-- The polynomial used by Shoup's contract reads the same coefficient bits. -/
theorem coeff_polyOfBits (l : BitStr) (i : ℕ) :
    (polyOfBits l).coeff i = ofBool (l.getD i false) := by
  simp only [polyOfBits, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]
  rw [Finset.sum_ite_eq']
  by_cases hi : i < l.length
  · simp [hi, ofBool]
  · simp [hi, ofBool, List.getD_eq_getElem?_getD]
end
end MIPRE.LowDegree.BinaryPolynomial

namespace MIPRE.LowDegree.BinaryPolynomial
section
open Cost
/-- A monic polynomial's leading coefficient is present in its coefficient list. -/
theorem natDegree_lt_length (l : BitStr) (h : (polyOfBits l).Monic) :
    (polyOfBits l).natDegree < l.length := by
  have hc : (polyOfBits l).coeff (polyOfBits l).natDegree = 1 := h.coeff_natDegree
  by_contra hn
  rw [coeff_polyOfBits] at hc
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega :
    l.length ≤ (polyOfBits l).natDegree), ofBool] at hc
end
end MIPRE.LowDegree.BinaryPolynomial

namespace MIPRE.LowDegree.BinaryPolynomial
section
open Cost Cost.PolyTimeFun Polynomial
theorem fold_traceStep_length (u : Unary) (p a c : BitStr)
    (ha : a.length = p.length) (hc : c.length = p.length) :
    (u.foldl traceStep (p, a, c)).2.1.length = p.length ∧
    (u.foldl traceStep (p, a, c)).2.2.length = p.length := by
  induction u generalizing a c with
  | nil => exact ⟨ha, hc⟩
  | cons b u ih =>
    exact ih _ _ (length_mulReduce _ _ _ ha) (by simp [length_xorBits, ha, hc])
end
end MIPRE.LowDegree.BinaryPolynomial

namespace MIPRE.LowDegree.BinaryPolynomial
section
open Cost Cost.PolyTimeFun Polynomial
theorem length_frobeniusTrace (p a : BitStr) (u : Unary) (ha : a.length = p.length) :
    (frobeniusTrace p a u).1.length = p.length ∧
    (frobeniusTrace p a u).2.length = p.length :=
  fold_traceStep_length u p a _ ha (length_zeroBits p)
end
end MIPRE.LowDegree.BinaryPolynomial

namespace MIPRE.LowDegree.BinaryPolynomial
section
open Cost Cost.PolyTimeFun Polynomial
variable {R : Type*} [CommRing R] [CharP R 2]
theorem evalBits_fold_traceStep (z : R) (p a c : BitStr) (u : Unary)
    (hroot : z ^ p.length = evalBits z p)
    (ha : a.length = p.length) (hc : c.length = p.length) :
    evalBits z (u.foldl traceStep (p, a, c)).2.1 = evalBits z a ^ (2 ^ u.length) ∧
    evalBits z (u.foldl traceStep (p, a, c)).2.2 =
      evalBits z c + ∑ i ∈ Finset.range u.length, evalBits z a ^ (2 ^ i) := by
  induction u generalizing a c with
  | nil => simp
  | cons b u ih =>
    obtain ⟨hi, hs⟩ := ih (mulReduce p a a) (xorBits c a)
      (length_mulReduce _ _ _ ha) (by simp [length_xorBits, ha, hc])
    change evalBits z (u.foldl traceStep (p, mulReduce p a a, xorBits c a)).2.1 = _ ∧
      evalBits z (u.foldl traceStep (p, mulReduce p a a, xorBits c a)).2.2 = _
    rw [hi, hs, evalBits_mulReduce z p a a ha hroot,
      evalBits_xor z c a (hc.trans ha.symm)]
    have hp (i : ℕ) : (evalBits z a * evalBits z a) ^ (2 ^ i) =
        evalBits z a ^ (2 ^ (i + 1)) := by
      rw [← pow_two, ← pow_mul, pow_succ']
    constructor
    · exact hp u.length
    · simp only [List.length_cons, Finset.sum_range_succ', hp, pow_zero, pow_one]
      ring
end
end MIPRE.LowDegree.BinaryPolynomial

namespace MIPRE.LowDegree.BinaryPolynomial
section
open Cost Cost.PolyTimeFun Polynomial
variable {R : Type*} [CommRing R] [CharP R 2]
/-- Squaring and accumulating computes the Frobenius orbit and its trace sum. -/
theorem evalBits_frobeniusTrace (z : R) (p a : BitStr) (u : Unary)
    (hroot : z ^ p.length = evalBits z p) (ha : a.length = p.length) :
    evalBits z (frobeniusTrace p a u).1 = evalBits z a ^ (2 ^ u.length) ∧
    evalBits z (frobeniusTrace p a u).2 =
      ∑ i ∈ Finset.range u.length, evalBits z a ^ (2 ^ i) := by
  have h := evalBits_fold_traceStep z p a (zeroBits p) u hroot ha (length_zeroBits p)
  simpa only [frobeniusTrace, evalBits_zeroBits, zero_add] using h
end
end MIPRE.LowDegree.BinaryPolynomial

namespace MIPRE.LowDegree.BinaryPolynomial
section
open Cost Cost.PolyTimeFun Polynomial
variable {R : Type*} [CommRing R] [CharP R 2]
/-- The accumulated sum is the algebraic trace, embedded into the extension field. -/
theorem evalBits_frobeniusTrace_trace {F : Type*} [Field F] [Finite F] [CharP F 2]
    [Algebra (ZMod 2) F] (z : F) (p a : BitStr)
    (hdegree : Module.finrank (ZMod 2) F = p.length)
    (hroot : z ^ p.length = evalBits z p) (ha : a.length = p.length) :
    evalBits z (frobeniusTrace p a (unary p.length)).2 =
      algebraMap (ZMod 2) F (Algebra.trace (ZMod 2) F (evalBits z a)) := by
  rw [(evalBits_frobeniusTrace z p a _ hroot ha).2,
    FiniteField.algebraMap_trace_eq_sum_pow, hdegree, length_unary]
  simp
end
end MIPRE.LowDegree.BinaryPolynomial

namespace MIPRE.LowDegree.BinaryPolynomial
section
open Cost
theorem shoupLowerCoeffs_length (k : ℕ) (hk : 1 ≤ k) :
    (shoupLowerCoeffs (unary k)).length = k := by
  have h := natDegree_lt_length (shoupIrreducible (unary k)) (shoupIrreducible_monic k hk)
  rw [shoupIrreducible_natDegree k hk] at h
  simp [shoupLowerCoeffs, min_eq_left (by omega : k ≤ (shoupIrreducible (unary k)).length)]
end
end MIPRE.LowDegree.BinaryPolynomial

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.SAT
open Cost LowDegree LowDegree.BinaryPolynomial
theorem _root_.solution (k : ℕ) (hk : 1 ≤ k)
    (a : (shoupBinField k hk).carrier) :
    shoupTraceProg (unary k, (shoupBinField k hk).toBits a) =
      (shoupBinField k hk).toBits
        (algebraMap (ZMod 2) (shoupBinField k hk).carrier
          (Algebra.trace (ZMod 2) (shoupBinField k hk).carrier a)) := by
  have hw : ((shoupBinField k hk).toBits a).length =
      (shoupLowerCoeffs (unary k)).length := by
    rw [(shoupBinField k hk).length_toBits, shoupLowerCoeffs_length k hk]
  apply (shoupRoot_eval_eq_iff k hk _ _
    ((length_frobeniusTrace _ _ (unary k) hw).2.trans (shoupLowerCoeffs_length k hk))
    ((shoupBinField k hk).length_toBits _)).mp
  rw [shoupRoot_eval_toBits]
  have h := evalBits_frobeniusTrace_trace (shoupRoot k hk) _ _
    ((shoupBinField_finrank k hk).trans (shoupLowerCoeffs_length k hk).symm)
    (shoupRoot_equation k hk) hw
  rw [shoupLowerCoeffs_length k hk, shoupRoot_eval_toBits] at h
  exact h
end MIPRE.SAT
