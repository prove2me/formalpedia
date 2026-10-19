-- Prove2me | solution 1 for MIPRE.QLD.PauliQuestionProgram.gammaProg_fieldEncoding
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T06:35:20.329266+00:00
-- url     : https://prove2.me/submissions/ad95db46-eb83-4ccf-88ba-71283b5a3ad0

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/QLD/PauliQuestionPrograms.lean (solution of MIPRE.QLD.PauliQuestionProgram.gammaProg_fieldEncoding);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.Star.Module
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Sum
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Basic
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Rotate
import Mathlib.Data.Matrix.Basic
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
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Matrix.Circulant
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Pi
import Mathlib.Order.Fin.Basic
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.Polynomial.Content
import Mathlib.RingTheory.Polynomial.Cyclotomic.Factorization
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Background_LIDT_Game
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Canonical
import Definitions.Def_MIPRE_Background_LIDT_CLGame
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
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_Foundations_POVMValue
import Definitions.Def_MIPRE_Foundations_PVM
import Definitions.Def_MIPRE_Foundations_PVM_B
import Definitions.Def_MIPRE_Foundations_LowDegree_SchwartzZippel
import Definitions.Def_MIPRE_Foundations_LowDegree_Anticomm
import Definitions.Def_MIPRE_Foundations_GameAdapt
import Definitions.Def_MIPRE_Foundations_RegisterReindex
import Definitions.Def_MIPRE_Foundations_RegisterReindex_B
import Definitions.Def_MIPRE_Foundations_SampledGame
import Definitions.Def_MIPRE_Foundations_CL_Downsize
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
import Definitions.Def_MIPRE_Foundations_Cost_BinaryArithmetic
import Definitions.Def_MIPRE_Foundations_Introspection_SeedSelectorProg
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
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryInverse
import Definitions.Def_MIPRE_Foundations_Introspection_LineRepresentativeProg
import Definitions.Def_MIPRE_Foundations_Cost_BinaryCompare
import Definitions.Def_MIPRE_Foundations_Introspection_SeededLineProg
import Definitions.Def_MIPRE_Foundations_Cost_TreeBits
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgFinite
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgParse
import Definitions.Def_MIPRE_Background_LIDT_Adapter_Geometry
import Definitions.Def_MIPRE_Foundations_Introspection_FieldPolynomialProg
import Definitions.Def_MIPRE_Foundations_Introspection_FieldLineCheckProg
import Definitions.Def_MIPRE_Foundations_Introspection_PauliStageProg
import Definitions.Def_MIPRE_Foundations_Introspection_PauliStageProg_B
import Definitions.Def_MIPRE_Foundations_Introspection_FieldQuestionProg
import Definitions.Def_MIPRE_LCS_Basic
import Definitions.Def_MIPRE_LCS_Common
import Definitions.Def_MIPRE_LCS_Measurement
import Definitions.Def_MIPRE_LCS_Observable
import Definitions.Def_MIPRE_LCS_Strategy_ObservableToProjector
import Definitions.Def_MIPRE_LCS_NonlocalGame
import Definitions.Def_MIPRE_LCS_Pauli
import Definitions.Def_MIPRE_LCS_MagicSquare_Strategy
import Definitions.Def_MIPRE_LCS_MagicSquare_Game
import Definitions.Def_MIPRE_Background_QLD_Game
import Definitions.Def_MIPRE_Background_QLD_CLPresentation
import Definitions.Def_MIPRE_Background_QLD_CLBinary
import Definitions.Def_MIPRE_Background_QLD_CLExplicitSeed
import Definitions.Def_MIPRE_Background_QLD_PauliStagePrograms
import Definitions.Def_MIPRE_Background_QLD_TypeEncoding
import Definitions.Def_MIPRE_Foundations_Introspection_FieldIndicatorProg
import Definitions.Def_MIPRE_Foundations_Introspection_FieldTableProg
import Definitions.Def_MIPRE_Background_QLD_PauliBranchPrograms
import Definitions.Def_MIPRE_Foundations_Introspection_FieldGammaProg
import Definitions.Def_MIPRE_Background_QLD_PauliArithmeticPrograms
import Theorems.Thm_MIPRE_LowDegree_BinaryLinear_xorBits_vectorBits
import Theorems.Thm_MIPRE_LowDegree_BinaryPolynomial_evalBits_oneBits
import Theorems.Thm_MIPRE_SAT_shoupBinField_charP
import Theorems.Thm_MIPRE_SAT_shoupMulProg_encoding
import Theorems.Thm_MIPRE_SAT_shoupRoot_eval_eq_iff
import Theorems.Thm_MIPRE_SAT_shoupRoot_eval_toBits
import Theorems.Thm_MIPRE_SAT_shoupTraceBitProg_correct

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

namespace MIPRE.Introspection.FieldGammaProgram
noncomputable section
open Cost Cost.PolyTimeFun SAT LowDegree LowDegree.BinaryPolynomial LowDegree.BinaryLinear FieldIndicatorProgram
theorem indPair_eq_prod {K : Type*} [CommRing K] {m : ℕ} (x z : Fin m → K) :
    indPair x z = ∏ i, ((1 - x i) * (1 - z i) + x i * z i) := by
  classical
  have h := Finset.prod_univ_sum (fun _ : Fin m => (Finset.univ : Finset Bool))
    (fun i b => (if b then x i else 1 - x i) * (if b then z i else 1 - z i))
  rw [Fintype.piFinset_univ] at h
  have hsum : ∀ i : Fin m,
      (∑ b : Bool, (if b then x i else 1 - x i) * (if b then z i else 1 - z i)) =
      (1 - x i) * (1 - z i) + x i * z i := by
    intro i
    simp [add_comm]
  rw [Finset.prod_congr rfl fun i _ => hsum i] at h
  rw [indPair]
  rw [Finset.sum_congr rfl fun y _ => by
    rw [indVec_apply, indVec_apply, ← Finset.prod_mul_distrib]]
  exact h.symm
end
end MIPRE.Introspection.FieldGammaProgram

namespace MIPRE.Introspection.FieldGammaProgram
noncomputable section
open Cost Cost.PolyTimeFun SAT LowDegree LowDegree.BinaryPolynomial LowDegree.BinaryLinear FieldIndicatorProgram
theorem indPair_eq_prod_charTwo {K : Type*} [CommRing K] [CharP K 2]
    {m : ℕ} (x z : Fin m → K) : indPair x z = ∏ i, (1 + x i + z i) := by
  rw [indPair_eq_prod]
  apply Finset.prod_congr rfl
  intro i _
  simp only [CharTwo.sub_eq_add]
  calc
    (1 + x i) * (1 + z i) + x i * z i =
        1 + x i + z i + (x i * z i + x i * z i) := by ring
    _ = _ := by rw [CharTwo.add_self_eq_zero, add_zero]
end
end MIPRE.Introspection.FieldGammaProgram

namespace MIPRE.Introspection.FieldGammaProgram
noncomputable section
open Cost Cost.PolyTimeFun SAT LowDegree LowDegree.BinaryPolynomial LowDegree.BinaryLinear FieldIndicatorProgram
theorem pairFactorProg_correct (k : ℕ) (hk : 1 ≤ k)
    (x z : (shoupBinField k hk).carrier) :
    pairFactorProg ((shoupBinField k hk).toBits x, (shoupBinField k hk).toBits z) =
      (shoupBinField k hk).toBits (1 + x + z) := by
  change xorBits (xorBits (oneBits ((shoupBinField k hk).toBits x))
    ((shoupBinField k hk).toBits x)) ((shoupBinField k hk).toBits z) = _
  rw [shoupBinField_oneBits k hk _ ((shoupBinField k hk).length_toBits x),
    shoupXorBits_correct, shoupXorBits_correct]
end
end MIPRE.Introspection.FieldGammaProgram

namespace MIPRE.Introspection.FieldGammaProgram
noncomputable section
open Cost Cost.PolyTimeFun SAT LowDegree LowDegree.BinaryPolynomial LowDegree.BinaryLinear FieldIndicatorProgram
theorem pairingProg_correct (k : ℕ) (hk : 1 ≤ k) {m : ℕ}
    (x z : Fin m → (shoupBinField k hk).carrier) :
    pairingProg (unary k,
      List.ofFn fun i => ((shoupBinField k hk).toBits (x i),
        (shoupBinField k hk).toBits (z i))) =
      (shoupBinField k hk).toBits (indPair x z) := by
  have hmap :
      (List.ofFn fun i => ((shoupBinField k hk).toBits (x i),
        (shoupBinField k hk).toBits (z i))).map pairFactorProg =
      (List.ofFn fun i => 1 + x i + z i).map (shoupBinField k hk).toBits := by
    simp only [List.map_ofFn, Function.comp_def, pairFactorProg_correct]
  change arithmeticFold true (shoupLowerCoeffs (unary k))
    (oneBits (shoupZeroProg (unary k)))
    ((List.ofFn fun i => ((shoupBinField k hk).toBits (x i),
      (shoupBinField k hk).toBits (z i))).map pairFactorProg) = _
  rw [hmap, shoupZeroProg_correct k hk,
    shoupBinField_oneBits k hk _ ((shoupBinField k hk).length_toBits 0),
    shoupArithmeticFold_mul_correct, one_mul, List.prod_ofFn, indPair_eq_prod_charTwo]
end
end MIPRE.Introspection.FieldGammaProgram

namespace MIPRE.Introspection.FieldGammaProgram
noncomputable section
open Cost Cost.PolyTimeFun SAT LowDegree LowDegree.BinaryPolynomial LowDegree.BinaryLinear FieldIndicatorProgram
theorem gammaProg_correct (k : ℕ) (hk : 1 ≤ k) {m : ℕ}
    (x z : Fin m → (shoupBinField k hk).carrier)
    (rX rZ : (shoupBinField k hk).carrier) :
    gammaProg (unary k,
      List.ofFn (fun i => ((shoupBinField k hk).toBits (x i),
        (shoupBinField k hk).toBits (z i))),
      (shoupBinField k hk).toBits rX, (shoupBinField k hk).toBits rZ) =
      bit (acGamma (ZMod 2) x z rX rZ) := by
  simp only [gammaProg, comp_apply, pair_apply, fst_apply, snd_apply]
  rw [pairingProg_correct, shoupMulProg_encoding, shoupMulProg_encoding,
    shoupTraceBitProg_correct]
  rfl
end
end MIPRE.Introspection.FieldGammaProgram

namespace MIPRE.QLD.PauliArithmeticProgram
noncomputable section
open Cost Cost.PolyTimeFun SAT LowDegree.BinaryLinear Introspection.FieldLineCheck Introspection.FieldTableProgram Introspection.FieldGammaProgram
/-- The trace commutation bit used by rules four through seven. -/
theorem gammaProg_eq_gam (k : ℕ) (hk : 1 ≤ k) {m : ℕ}
    (ω : Omega (shoupBinField k hk).carrier m) :
    gammaProg (unary k,
      List.ofFn (fun i => ((shoupBinField k hk).toBits (ω.uX i),
        (shoupBinField k hk).toBits (ω.uZ i))),
      (shoupBinField k hk).toBits ω.rX, (shoupBinField k hk).toBits ω.rZ) =
      bit (gam ω) := gammaProg_correct k hk ω.uX ω.uZ ω.rX ω.rZ
end
end MIPRE.QLD.PauliArithmeticProgram

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.QLD.PauliQuestionProgram
open Cost SAT Introspection.FieldQuestionProgram Introspection.SeedProgram PauliCL PauliBranchProgram
theorem _root_.solution (k : ℕ) (hk : 1 ≤ k) {m : ℕ}
    (x : Coord m → (shoupBinField k hk).carrier) :
    Introspection.FieldGammaProgram.gammaProg (unary k,
      (Introspection.PauliStageProgram.pointX (fieldEncoding (shoupBinField k hk) x)).zip
        (Introspection.PauliStageProgram.pointZ (fieldEncoding (shoupBinField k hk) x)),
      Introspection.PauliStageProgram.scalarX (fieldEncoding (shoupBinField k hk) x),
      Introspection.PauliStageProgram.scalarZ (fieldEncoding (shoupBinField k hk) x)) =
      LowDegree.BinaryLinear.bit (gam (vectorContent x).omega) := by
  have hz : ((shoupBinField k hk).vecBits (fun i => x (.point .X i))).zip
      ((shoupBinField k hk).vecBits (fun i => x (.point .Z i))) =
      List.ofFn (fun i => ((shoupBinField k hk).toBits (x (.point .X i)),
        (shoupBinField k hk).toBits (x (.point .Z i)))) := by
    apply List.ext_getElem <;> simp [BinField.vecBits]
  change Introspection.FieldGammaProgram.gammaProg (unary k, _,
    (shoupBinField k hk).toBits (x (.scalar .X)),
    (shoupBinField k hk).toBits (x (.scalar .Z))) = _
  simp only [Introspection.PauliStageProgram.pointX, Introspection.PauliStageProgram.pointZ,
    Cost.PolyTimeFun.fst_apply, Cost.PolyTimeFun.snd_apply, Cost.PolyTimeFun.comp_apply,
    fieldEncoding, hz]
  exact PauliArithmeticProgram.gammaProg_eq_gam k hk (vectorContent x).omega
end MIPRE.QLD.PauliQuestionProgram
