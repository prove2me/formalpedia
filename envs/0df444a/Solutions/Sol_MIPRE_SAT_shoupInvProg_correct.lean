-- Prove2me | solution 1 for MIPRE.SAT.shoupInvProg_correct
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T05:32:35.103539+00:00
-- url     : https://prove2.me/submissions/e8c40d26-2ec3-4190-8390-e15aa4195a49

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/LowDegree/BinaryInverse.lean (solution of MIPRE.SAT.shoupInvProg_correct);
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
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryInverse
import Theorems.Thm_MIPRE_LowDegree_BinaryPolynomial_evalBits_mulReduce
import Theorems.Thm_MIPRE_LowDegree_BinaryPolynomial_evalBits_oneBits
import Theorems.Thm_MIPRE_LowDegree_BinaryPolynomial_length_mulReduce
import Theorems.Thm_MIPRE_LowDegree_shoupIrreducible_monic
import Theorems.Thm_MIPRE_LowDegree_shoupIrreducible_natDegree
import Theorems.Thm_MIPRE_SAT_shoupBinField_charP
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
theorem fold_powerStep_length (l : BitStr) (p a c : BitStr)
    (ha : a.length = p.length) (hc : c.length = p.length) :
    (l.foldl powerStep (p, a, c)).2.2.length = p.length := by
  induction l generalizing a c with
  | nil => exact hc
  | cons b l ih =>
    change (l.foldl powerStep
      (p, mulReduce p a a, if b then mulReduce p c a else c)).2.2.length = _
    apply ih _ _ (length_mulReduce _ _ _ ha)
    cases b
    · exact hc
    · exact length_mulReduce _ _ _ hc
end
end MIPRE.LowDegree.BinaryPolynomial

namespace MIPRE.LowDegree.BinaryPolynomial
section
open Cost Cost.PolyTimeFun Polynomial
theorem length_powerBits (p a e : BitStr) (ha : a.length = p.length) :
    (powerBits p a e).length = p.length :=
  fold_powerStep_length e p a (oneBits p) ha (length_oneBits p)
end
end MIPRE.LowDegree.BinaryPolynomial

namespace MIPRE.LowDegree.BinaryPolynomial
section
open Cost Cost.PolyTimeFun Polynomial
variable {R : Type*} [CommRing R] [CharP R 2]
theorem evalBits_fold_powerStep (z : R) (p a c e : BitStr)
    (hroot : z ^ p.length = evalBits z p)
    (ha : a.length = p.length) (hc : c.length = p.length) :
    evalBits z (e.foldl powerStep (p, a, c)).2.2 =
      evalBits z c * evalBits z a ^ bitsVal e := by
  induction e generalizing a c with
  | nil => simp [bitsVal]
  | cons b e ih =>
    change evalBits z (e.foldl powerStep
      (p, mulReduce p a a, if b then mulReduce p c a else c)).2.2 = _
    cases b
    · simp only [Bool.false_eq_true, if_false]
      rw [ih _ _ (length_mulReduce _ _ _ ha) hc, evalBits_mulReduce z p a a ha hroot]
      simp [bitsVal_cons, Nat.bit, pow_mul, pow_two]
    · simp only [if_true]
      rw [ih _ _ (length_mulReduce _ _ _ ha) (length_mulReduce _ _ _ hc),
        evalBits_mulReduce z p a a ha hroot, evalBits_mulReduce z p c a hc hroot]
      simp only [bitsVal_cons, Nat.bit, Bool.cond_true]
      rw [pow_add, pow_one, pow_mul]
      ring
end
end MIPRE.LowDegree.BinaryPolynomial

namespace MIPRE.LowDegree.BinaryPolynomial
section
open Cost Cost.PolyTimeFun Polynomial
variable {R : Type*} [CommRing R] [CharP R 2]
/-- Correctness for every characteristic-two ring containing a root of the modulus. -/
theorem evalBits_powerBits (z : R) (p a e : BitStr) (hp : p ≠ [])
    (hroot : z ^ p.length = evalBits z p) (ha : a.length = p.length) :
    evalBits z (powerBits p a e) = evalBits z a ^ bitsVal e := by
  rw [powerBits, evalBits_fold_powerStep z p a _ e hroot ha (length_oneBits p),
    evalBits_oneBits z p hp, one_mul]
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

namespace MIPRE.LowDegree.BinaryPolynomial
section
open Cost Cost.PolyTimeFun
theorem bitsVal_ones (n : ℕ) : bitsVal (List.replicate n true) + 1 = 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [List.replicate_succ, bitsVal_cons, Nat.bit, Bool.cond_true, pow_succ]
    omega
end
end MIPRE.LowDegree.BinaryPolynomial

namespace MIPRE.LowDegree.BinaryPolynomial
section
open Cost Cost.PolyTimeFun
theorem bitsVal_inverseExponent (p : BitStr) :
    bitsVal (inverseExponent p) = 2 ^ p.length - 2 := by
  cases p with
  | nil => rfl
  | cons b p =>
    have h := bitsVal_ones p.length
    have hm : p.map (fun _ => true) = List.replicate p.length true := by simp
    simp only [inverseExponent, List.tail_cons, hm, bitsVal_cons, Nat.bit,
      Bool.cond_false, List.length_cons, pow_succ]
    omega
end
end MIPRE.LowDegree.BinaryPolynomial

namespace MIPRE.LowDegree.BinaryPolynomial
section
open Cost Cost.PolyTimeFun
theorem length_inverseBits (p a : BitStr) (ha : a.length = p.length) :
    (inverseBits p a).length = p.length := length_powerBits _ _ _ ha
end
end MIPRE.LowDegree.BinaryPolynomial

namespace MIPRE.LowDegree.BinaryPolynomial
section
open Cost Cost.PolyTimeFun
/-- Correctness in every finite characteristic-two field of the supplied cardinality. -/
theorem evalBits_inverseBits {F : Type*} [Field F] [Fintype F] [CharP F 2]
    (z : F) (p a : BitStr) (hp : p ≠ [])
    (hcard : Fintype.card F = 2 ^ p.length)
    (hroot : z ^ p.length = evalBits z p)
    (ha : a.length = p.length) (hne : evalBits z a ≠ 0) :
    evalBits z (inverseBits p a) = (evalBits z a)⁻¹ := by
  rw [inverseBits, evalBits_powerBits z p a _ hp hroot ha, bitsVal_inverseExponent, ← hcard]
  apply eq_inv_of_mul_eq_one_left
  rw [← pow_succ]
  have hq : 2 ≤ Fintype.card F := Fintype.one_lt_card
  rw [show Fintype.card F - 2 + 1 = Fintype.card F - 1 by omega]
  exact FiniteField.pow_card_sub_one_eq_one _ hne
end
end MIPRE.LowDegree.BinaryPolynomial

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.SAT
open Cost LowDegree LowDegree.BinaryPolynomial
theorem _root_.solution (k : ℕ) (hk : 1 ≤ k)
    (a : (shoupBinField k hk).carrier) (ha : a ≠ 0) :
    shoupInvProg (unary k, (shoupBinField k hk).toBits a) =
      (shoupBinField k hk).toBits a⁻¹ := by
  have hp : shoupLowerCoeffs (unary k) ≠ [] := by
    intro he
    have := shoupLowerCoeffs_length k hk
    rw [he] at this
    simp only [List.length_nil] at this
    omega
  have hwidth : ((shoupBinField k hk).toBits a).length =
      (shoupLowerCoeffs (unary k)).length := by
    rw [(shoupBinField k hk).length_toBits, shoupLowerCoeffs_length k hk]
  have hi := evalBits_inverseBits (shoupRoot k hk) (shoupLowerCoeffs (unary k))
    ((shoupBinField k hk).toBits a) hp
    (by rw [shoupLowerCoeffs_length k hk]; exact (shoupBinField k hk).card_carrier)
    (shoupRoot_equation k hk) hwidth (by rwa [shoupRoot_eval_toBits])
  apply (shoupRoot_eval_eq_iff k hk _ _
    ((length_inverseBits _ _ hwidth).trans (shoupLowerCoeffs_length k hk))
    ((shoupBinField k hk).length_toBits _)).mp
  rw [shoupRoot_eval_toBits]
  simpa only [shoupRoot_eval_toBits] using hi
end MIPRE.SAT
