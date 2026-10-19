-- Prove2me | solution 1 for MIPRE.QLD.PauliCL.linearBits_correct
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T06:49:40.24773+00:00
-- url     : https://prove2.me/submissions/0ec97c49-d85d-48f3-b029-24d0bde3af2a

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/QLD/PauliRowPrograms.lean (solution of MIPRE.QLD.PauliCL.linearBits_correct);
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
import Mathlib.Algebra.Polynomial.Eval.Degree
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
import Mathlib.Computability.Primrec.List
import Mathlib.Data.Complex.Basic
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Sum
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Basic
import Mathlib.Data.List.GetD
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
import Mathlib.Logic.Denumerable
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
import Definitions.Def_MIPRE_Foundations_Cost_Codable_B
import Definitions.Def_MIPRE_Foundations_Halting_Descriptions
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
import Definitions.Def_MIPRE_Foundations_SAT_BasisTransport
import Definitions.Def_MIPRE_Foundations_SAT_EffectiveSelfDual
import Definitions.Def_MIPRE_Foundations_SAT_EffectiveNormalBasis
import Definitions.Def_MIPRE_Foundations_Introspection_BasisProg
import Definitions.Def_MIPRE_Foundations_Introspection_BinaryBlockProg
import Definitions.Def_MIPRE_Foundations_Introspection_BinaryBlockProg_B
import Definitions.Def_MIPRE_Background_LIDT_Adapter_Geometry
import Definitions.Def_MIPRE_Foundations_Introspection_PauliStageProg
import Definitions.Def_MIPRE_Foundations_Introspection_PauliStageProg_B
import Definitions.Def_MIPRE_Foundations_Halting_Lists_B
import Definitions.Def_MIPRE_Foundations_Cost_Growth
import Definitions.Def_MIPRE_Foundations_Halting_Arith
import Definitions.Def_MIPRE_Foundations_Halting_Arith_B
import Definitions.Def_MIPRE_Foundations_Repeat_Prims
import Definitions.Def_MIPRE_Foundations_CL_Repeat
import Definitions.Def_MIPRE_Foundations_Repeat_Bits
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
import Definitions.Def_MIPRE_Background_QLD_BinaryBlocks
import Definitions.Def_MIPRE_Foundations_Introspection_PauliRowsProg
import Theorems.Thm_MIPRE_CL_CLFun_mapOfPrefix_downsize
import Theorems.Thm_MIPRE_CL_CLFun_mapOfPrefix_reindex
import Theorems.Thm_MIPRE_Introspection_LineProgram_lineRepresentativeProg_correct
import Theorems.Thm_MIPRE_LIDT_Adapter_pivots_line
import Theorems.Thm_MIPRE_LowDegree_BinaryLinear_groupComponentsProg_correct
import Theorems.Thm_MIPRE_LowDegree_BinaryLinear_inverseRootMatrixProg_correct
import Theorems.Thm_MIPRE_LowDegree_BinaryLinear_mulBits_matrixBits
import Theorems.Thm_MIPRE_LowDegree_BinaryLinear_transposeBits_matrixBits
import Theorems.Thm_MIPRE_LowDegree_BinaryLinear_xorBits_vectorBits
import Theorems.Thm_MIPRE_QLD_PauliCL_binaryVectorEquiv_bits
import Theorems.Thm_MIPRE_QLD_PauliCL_representative_eq_canonLin
import Theorems.Thm_MIPRE_SAT_shoupActionProg_correct
import Theorems.Thm_MIPRE_SAT_shoupBinField_finrank
import Theorems.Thm_MIPRE_SAT_shoupInBasisProg_correct
import Theorems.Thm_MIPRE_SAT_shoupMulProg_encoding
import Theorems.Thm_MIPRE_SAT_shoupNormalBasis_normal
import Theorems.Thm_MIPRE_SAT_shoupTraceGramProg_correct

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.SAT
section
open Cost
theorem bitsVal_cons' (b : Bool) (l : BitStr) : bitsVal (b :: l) = 2 * bitsVal l + b.toNat := by
  rw [bitsVal_cons]; cases b <;> simp [Nat.bit]
end
end MIPRE.SAT

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
open Cost LowDegree LowDegree.BinaryPolynomial LowDegree.BinaryLinear
attribute [local instance] MIPRE.SAT.instFactPrimeOfNatNat_mIPRE_1
/-- Standard unit vectors encode the corresponding polynomial-basis elements. -/
theorem shoupPowerBasis_encoding (k : ℕ) (hk : 1 ≤ k) (j : Fin k) :
    (shoupBinField k hk).toBits (shoupPowerBasis k hk j) = unitBits k j := by
  rw [← shoupCoordinateEquiv_encoding, shoupPowerBasis, Module.Basis.coe_ofEquivFun,
    LinearEquiv.apply_symm_apply, unitBits_eq_vectorBits]
end
end MIPRE.SAT

namespace MIPRE.Introspection.SeedProgram
noncomputable section
open Cost Cost.PolyTimeFun SAT
theorem bitsVal_drop (l : BitStr) (n : ℕ) :
    bitsVal (l.drop n) = bitsVal l / 2 ^ n := by
  induction n generalizing l with
  | zero => simp
  | succ n ih =>
    cases l with
    | nil => simp
    | cons b l =>
      rw [List.drop_succ_cons, ih, SAT.bitsVal_cons', pow_succ,
        Nat.mul_comm (2 ^ n) 2, ← Nat.div_div_eq_div_mul]
      have h : (2 * bitsVal l + b.toNat) / 2 = bitsVal l := by
        cases b
        · simp
        · simp only [Bool.toNat_true]; omega
      rw [h]
end
end MIPRE.Introspection.SeedProgram

namespace MIPRE.Introspection.SeedProgram
noncomputable section
open Cost Cost.PolyTimeFun SAT
/-- The exact connection between the equal-block selector and its bit scan. -/
theorem selector_eq_bits {k : ℕ} (E : BinField k) (j : ℕ) (hj : j ≤ k) (a : E.carrier) :
    (selector E j hj a).val = bitsVal ((E.toBits a).drop (k - j)) := by
  rw [bitsVal_drop]
  rfl
end
end MIPRE.Introspection.SeedProgram

namespace MIPRE.Introspection.SeedProgram
noncomputable section
open Cost Cost.PolyTimeFun SAT
theorem selectorProg_apply (k j : Unary) (s : BitStr) :
    selectorProg (k, j, s) = bitsVal (s.drop (k.length - j.length)) := by
  change bitsVal (s.drop (k.drop j.length).length) = _
  rw [List.length_drop]
end
end MIPRE.Introspection.SeedProgram

namespace MIPRE.Introspection.SeedProgram
noncomputable section
open Cost Cost.PolyTimeFun SAT
theorem selectorProg_correct {k : ℕ} (E : BinField k) (j : ℕ) (hj : j ≤ k) (a : E.carrier) :
    selectorProg (unary k, unary j, E.toBits a) = (selector E j hj a).val := by
  rw [selectorProg_apply, length_unary, length_unary, selector_eq_bits]
end
end MIPRE.Introspection.SeedProgram

namespace MIPRE.SAT
noncomputable section
open Cost LowDegree LowDegree.BinaryLinear LowDegree.BinaryPolynomial
theorem shoupSquareProg_correct (k : ℕ) (hk : 1 ≤ k)
    (a : (shoupBinField k hk).carrier) :
    shoupSquareProg (unary k, (shoupBinField k hk).toBits a) =
      (shoupBinField k hk).toBits (shoupFrobeniusLinear k hk a) := by
  change shoupMulProg (unary k, (shoupBinField k hk).toBits a,
    (shoupBinField k hk).toBits a) = _
  rw [shoupMulProg_encoding, shoupFrobeniusLinear_apply, pow_two]
end
end MIPRE.SAT

namespace MIPRE.SAT
noncomputable section
open Cost Cost.PolyTimeFun LowDegree LowDegree.BinaryLinear Polynomial
theorem shoupSquareStateProg_iterate_correct (k : ℕ) (hk : 1 ≤ k)
    (a : (shoupBinField k hk).carrier) (n : ℕ) :
    ((shoupSquareStateProg : (Unary × BitStr) → (Unary × BitStr))^[n]
      (unary k, (shoupBinField k hk).toBits a)) =
    (unary k, (shoupBinField k hk).toBits (a ^ (2 ^ n))) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih]
    change (unary k, shoupSquareProg (unary k, (shoupBinField k hk).toBits (a ^ (2 ^ n)))) = _
    rw [shoupSquareProg_correct, shoupFrobeniusLinear_apply, ← pow_mul, ← pow_succ]
end
end MIPRE.SAT

namespace MIPRE.SAT
noncomputable section
open Cost Cost.PolyTimeFun LowDegree LowDegree.BinaryLinear Polynomial
theorem shoupOrbitProg_correct (k : ℕ) (hk : 1 ≤ k) (a : (shoupBinField k hk).carrier) :
    shoupOrbitProg (unary k, (shoupBinField k hk).toBits a) =
      List.ofFn (fun i : Fin k => (shoupBinField k hk).toBits (a ^ (2 ^ i.val))) := by
  change (recordIterates (shoupSquareStateProg : (Unary × BitStr) → (Unary × BitStr))
    (unary k) (unary k, (shoupBinField k hk).toBits a)).map Prod.snd = _
  simp only [recordIterates, length_unary, List.map_ofFn, shoupSquareStateProg_iterate_correct]
  rfl
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

namespace MIPRE.SAT
noncomputable section
open Cost Cost.PolyTimeFun LowDegree LowDegree.BinaryLinear Polynomial
attribute [local instance] MIPRE.SAT.instFactPrimeOfNatNat_mIPRE_6
theorem firstNonzeroBitsProg_correct (k : ℕ) (hk : 1 ≤ k)
    (l : List (shoupBinField k hk).carrier) :
    firstNonzeroBitsProg (l.map (shoupBinField k hk).toBits, (shoupBinField k hk).toBits 0) =
      (shoupBinField k hk).toBits (firstNonzero l) := by
  change (l.map (shoupBinField k hk).toBits).foldr
    (fun a s => if nonzeroRow a then a else s) _ = _
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.map_cons, List.foldr_cons, shoupNonzeroRow_correct, ih]
    by_cases ha : a = 0 <;> simp [ha, firstNonzero]
end
end MIPRE.SAT

namespace MIPRE.SAT
noncomputable section
open Cost Cost.PolyTimeFun LowDegree LowDegree.BinaryLinear Polynomial
attribute [local instance] MIPRE.SAT.instFactPrimeOfNatNat_mIPRE_6
theorem shoupProjectionImagesProg_correct (k : ℕ) (hk : 1 ≤ k) [NeZero k]
    (e : AddMonoidAlgebra (ZMod 2) (Fin k)) :
    shoupProjectionImagesProg (unary k, vectorBits (groupCoordinates k e)) =
      List.ofFn (fun j => (shoupBinField k hk).toBits
        (shoupFrobeniusAction k hk e (shoupPowerBasis k hk j))) := by
  have hu : identityBits k = List.ofFn (fun j => (shoupBinField k hk).toBits (shoupPowerBasis k hk j)) := by
    apply List.ext_getElem
    · simp [identityBits]
    · intro j hj hj'
      have hjk : j < k := by simpa [identityBits] using hj
      simp only [identityBits, List.getElem_map, List.getElem_range, List.getElem_ofFn]
      exact (shoupPowerBasis_encoding k hk (⟨j, hjk⟩ : Fin k)).symm
  change (identityBits (unary k).length).map
    (fun a => shoupActionProg (unary k, vectorBits (groupCoordinates k e), a)) = _
  rw [length_unary, hu, List.map_ofFn]
  congr 1
  funext j
  exact shoupActionProg_correct k hk e _
end
end MIPRE.SAT

namespace MIPRE.SAT
noncomputable section
open Cost Cost.PolyTimeFun LowDegree LowDegree.BinaryLinear Polynomial
attribute [local instance] MIPRE.SAT.instFactPrimeOfNatNat_mIPRE_6
theorem shoupProjectedVectorProg_correct (k : ℕ) (hk : 1 ≤ k) [NeZero k]
    (e : AddMonoidAlgebra (ZMod 2) (Fin k)) :
    shoupProjectedVectorProg (unary k, vectorBits (groupCoordinates k e)) =
      (shoupBinField k hk).toBits (shoupProjectedVector k hk e) := by
  change firstNonzeroBitsProg
    (shoupProjectionImagesProg (unary k, vectorBits (groupCoordinates k e)),
      shoupZeroProg (unary k)) = _
  rw [shoupProjectionImagesProg_correct k hk, shoupZeroProg_correct k hk]
  rw [show List.ofFn (fun j => (shoupBinField k hk).toBits
      (shoupFrobeniusAction k hk e (shoupPowerBasis k hk j))) =
    (List.ofFn (fun j => shoupFrobeniusAction k hk e (shoupPowerBasis k hk j))).map
      (shoupBinField k hk).toBits by rw [List.map_ofFn]; rfl]
  exact firstNonzeroBitsProg_correct k hk _
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

namespace MIPRE.SAT
noncomputable section
open Cost Cost.PolyTimeFun LowDegree LowDegree.BinaryLinear Polynomial
attribute [local instance] MIPRE.SAT.instFactPrimeOfNatNat_mIPRE_6
theorem shoupNormalElementProg_correct (k : ℕ) (hk : 1 ≤ k) [NeZero k] :
    shoupNormalElementProg (unary k) = (shoupBinField k hk).toBits (shoupNormalElement k hk) := by
  change shoupSumProg (unary k, (groupComponentsProg (unary k)).map
    (fun e => shoupProjectedVectorProg (unary k, e))) = _
  rw [groupComponentsProg_correct, List.map_map]
  simp only [Function.comp_def, shoupProjectedVectorProg_correct k hk]
  rw [show (groupComponents k).map (fun e => (shoupBinField k hk).toBits (shoupProjectedVector k hk e)) =
    ((groupComponents k).map (shoupProjectedVector k hk)).map (shoupBinField k hk).toBits by
      rw [List.map_map]; rfl, shoupSumProg_correct]
  congr 1
  simp [shoupNormalElement, List.get_eq_getElem]
end
end MIPRE.SAT

namespace MIPRE.SAT
noncomputable section
open Cost Cost.PolyTimeFun LowDegree LowDegree.BinaryLinear Polynomial
attribute [local instance] MIPRE.SAT.instFactPrimeOfNatNat_mIPRE_6
theorem shoupNormalBasisProg_correct (k : ℕ) (hk : 1 ≤ k) [NeZero k] (hodd : Odd k) :
    shoupNormalBasisProg (unary k) =
      List.ofFn (fun i => (shoupBinField k hk).toBits (shoupNormalBasis k hk hodd i)) := by
  change shoupOrbitProg (unary k, shoupNormalElementProg (unary k)) = _
  rw [shoupNormalElementProg_correct k hk, shoupOrbitProg_correct]
  simp only [shoupNormalBasis_apply]
end
end MIPRE.SAT

namespace MIPRE.Introspection.SeededLineProgram
noncomputable section
open Cost Cost.PolyTimeFun SAT SeedProgram LineProgram
theorem maskBeforeProg_apply (k : Unary) (i : ℕ) (v : List BitStr) :
    maskBeforeProg (k, i, v) = ((List.range' 0 v.length).zip v).map
      (fun p => if i ≤ p.1 then p.2 else shoupZeroProg k) := by
  simp [maskBeforeProg, maskBeforeStep, indexedRows_apply]
end
end MIPRE.Introspection.SeededLineProgram

namespace MIPRE.Introspection.SeededLineProgram
noncomputable section
open Cost Cost.PolyTimeFun SAT SeedProgram LineProgram
theorem maskBeforeProg_correct (k : ℕ) (hk : 1 ≤ k) {n : ℕ} (i : ℕ)
    (v : Fin n → (shoupBinField k hk).carrier) :
    maskBeforeProg (unary k, i, (shoupBinField k hk).vecBits v) =
      (shoupBinField k hk).vecBits (fun j => if j.val < i then 0 else v j) := by
  rw [maskBeforeProg_apply, shoupZeroProg_correct k hk]
  apply List.ext_getElem
  · simp [BinField.vecBits]
  · intro j hj hj'
    simp only [BinField.vecBits, List.length_map, List.length_ofFn,
      List.getElem_map, List.getElem_zip, List.getElem_range', zero_add,
      List.getElem_ofFn]
    by_cases h : i ≤ j
    · simp [h, Nat.not_lt.mpr h]
    · simp [h, Nat.lt_of_not_ge h]
end
end MIPRE.Introspection.SeededLineProgram

namespace MIPRE.Introspection.SeededLineProgram
noncomputable section
open Cost Cost.PolyTimeFun SAT SeedProgram LineProgram
theorem zeroCoordinateProg_apply (k : Unary) (i : ℕ) (v : List BitStr) :
    zeroCoordinateProg (k, i, v) = ((List.range' 0 v.length).zip v).map
      (fun p => if i = p.1 then shoupZeroProg k else p.2) := by
  simp [zeroCoordinateProg, zeroCoordinateStep, indexedRows_apply]
end
end MIPRE.Introspection.SeededLineProgram

namespace MIPRE.Introspection.SeededLineProgram
noncomputable section
open Cost Cost.PolyTimeFun SAT SeedProgram LineProgram
theorem zeroCoordinateProg_correct (k : ℕ) (hk : 1 ≤ k) {n : ℕ} (i : Fin n)
    (v : Fin n → (shoupBinField k hk).carrier) :
    zeroCoordinateProg (unary k, i.val, (shoupBinField k hk).vecBits v) =
      (shoupBinField k hk).vecBits (fun j => if j = i then 0 else v j) := by
  rw [zeroCoordinateProg_apply, shoupZeroProg_correct k hk]
  apply List.ext_getElem
  · simp [BinField.vecBits]
  · intro j hj hj'
    simp only [BinField.vecBits, List.length_map, List.length_ofFn,
      List.getElem_map, List.getElem_zip, List.getElem_range', zero_add,
      List.getElem_ofFn]
    by_cases h : i.val = j
    · simp [h, Fin.ext_iff, eq_comm]
    · simp [h, Fin.ext_iff, eq_comm]
end
end MIPRE.Introspection.SeededLineProgram

namespace MIPRE.Introspection.SeededLineProgram
noncomputable section
open Cost Cost.PolyTimeFun SAT SeedProgram LineProgram
theorem axisRepresentativeProg_correct (k : ℕ) (hk : 1 ≤ k) (j : ℕ) (hj : j ≤ k)
    (s : (shoupBinField k hk).carrier)
    (u : Fin (2 ^ j) → (shoupBinField k hk).carrier) :
    axisRepresentativeProg ((unary k, unary j, (shoupBinField k hk).toBits s),
      (shoupBinField k hk).vecBits u) =
      (shoupBinField k hk).vecBits
        (fun i => if i = selector (shoupBinField k hk) j hj s then 0 else u i) := by
  change zeroCoordinateProg (unary k, selectorProg (unary k, unary j,
    (shoupBinField k hk).toBits s), (shoupBinField k hk).vecBits u) = _
  rw [selectorProg_correct _ j hj, zeroCoordinateProg_correct]
end
end MIPRE.Introspection.SeededLineProgram

namespace MIPRE.Introspection.SeededLineProgram
noncomputable section
open Cost Cost.PolyTimeFun SAT SeedProgram LineProgram
theorem selectedDirectionProg_correct (k : ℕ) (hk : 1 ≤ k) (j : ℕ) (hj : j ≤ k)
    (s : (shoupBinField k hk).carrier)
    (v : Fin (2 ^ j) → (shoupBinField k hk).carrier) :
    selectedDirectionProg ((unary k, unary j, (shoupBinField k hk).toBits s),
      (shoupBinField k hk).vecBits v) =
      (shoupBinField k hk).vecBits
        (fun i => if i < selector (shoupBinField k hk) j hj s then 0 else v i) := by
  change maskBeforeProg (unary k, selectorProg (unary k, unary j,
    (shoupBinField k hk).toBits s), (shoupBinField k hk).vecBits v) = _
  rw [selectorProg_correct _ j hj, maskBeforeProg_correct]
  simp only [Fin.lt_def]
end
end MIPRE.Introspection.SeededLineProgram

namespace MIPRE.SAT
noncomputable section
open Cost LowDegree LowDegree.BinaryLinear
/-- The supplied basis vectors are exactly the columns of the change-of-basis matrix. -/
theorem shoupBasisMatrix_encoding (k : ℕ) (hk : 1 ≤ k)
    (b : Module.Basis (Fin k) (ZMod 2) (shoupBinField k hk).carrier) :
    transposeBits k (List.ofFn (fun i => (shoupBinField k hk).toBits (b i))) =
      matrixBits (shoupBasisMatrix k hk b) := by
  have hc : List.ofFn (fun i => (shoupBinField k hk).toBits (b i)) =
      matrixBits (shoupBasisMatrix k hk b).transpose := by
    apply congrArg List.ofFn
    funext j
    rw [← shoupCoordinateEquiv_encoding]
    congr 1
    funext i
    exact (LinearMap.toMatrix_apply b (shoupPowerBasis k hk) LinearMap.id i j).symm
  rw [hc, transposeBits_matrixBits, Matrix.transpose_transpose]
end
end MIPRE.SAT

namespace MIPRE.SAT
noncomputable section
open Cost LowDegree LowDegree.BinaryLinear
/-- Matrix application sends the new coordinates to the original coordinates. -/
theorem shoupBasisMatrix_mulVec (k : ℕ) (hk : 1 ≤ k)
    (b : Module.Basis (Fin k) (ZMod 2) (shoupBinField k hk).carrier)
    (a : (shoupBinField k hk).carrier) :
    (shoupBasisMatrix k hk b).mulVec (b.equivFun a) = shoupCoordinateEquiv k hk a :=
  LinearMap.toMatrix_mulVec_repr b (shoupPowerBasis k hk) LinearMap.id a
end
end MIPRE.SAT

namespace MIPRE.SAT
noncomputable section
open Cost LowDegree LowDegree.BinaryLinear
theorem shoupSelfDualBasis_apply (k : ℕ) (hk : 1 ≤ k) [NeZero k] (hodd : Odd k)
    (b : Module.Basis (Fin k) (ZMod 2) (shoupBinField k hk).carrier)
    (hb : IsNormalBasis b) (i : Fin k) :
    shoupSelfDualBasis k hk hodd b hb i = shoupSelfDualVectors k hk b i := by
  rw [shoupSelfDualBasis, coe_basisOfLinearIndependentOfCardEqFinrank]
end
end MIPRE.SAT

namespace MIPRE.SAT
noncomputable section
open Cost LowDegree LowDegree.BinaryLinear
/-- Polynomial-basis coordinates of the changed family are the matrix product columns. -/
theorem shoupChangedVectors_encoding (k : ℕ) (hk : 1 ≤ k)
    (b : Module.Basis (Fin k) (ZMod 2) (shoupBinField k hk).carrier)
    (H : Matrix (Fin k) (Fin k) (ZMod 2)) (j : Fin k) :
    (shoupBinField k hk).toBits (shoupChangedVectors k hk b H j) =
      vectorBits ((shoupBasisMatrix k hk b * H).col j) := by
  rw [← shoupCoordinateEquiv_encoding]
  congr 1
  funext i
  simp only [shoupChangedVectors, map_sum, map_smul, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, Matrix.col_apply, Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro r _
  rw [shoupBasisMatrix, LinearMap.toMatrix_apply]
  exact mul_comm _ _
end
end MIPRE.SAT

namespace MIPRE.SAT
noncomputable section
open Cost LowDegree LowDegree.BinaryLinear
/-- Every output vector is the canonical encoding of the constructed self-dual normal basis. -/
theorem shoupSelfDualizeProg_correct (k : ℕ) (hk : 1 ≤ k) [NeZero k] (hodd : Odd k)
    (b : Module.Basis (Fin k) (ZMod 2) (shoupBinField k hk).carrier)
    (hb : IsNormalBasis b) :
    shoupSelfDualizeProg (unary k, List.ofFn (fun i => (shoupBinField k hk).toBits (b i))) =
      List.ofFn (fun i => (shoupBinField k hk).toBits (shoupSelfDualBasis k hk hodd b hb i)) := by
  change transposeBits (unary k).length (mulBits (unary k).length
    (transposeBits (unary k).length (List.ofFn (fun i => (shoupBinField k hk).toBits (b i))))
    (inverseRootMatrixProg (unary k, shoupTraceGramProg
      (unary k, List.ofFn (fun i => (shoupBinField k hk).toBits (b i)))))) = _
  rw [length_unary, shoupBasisMatrix_encoding, shoupTraceGramProg_correct,
    inverseRootMatrixProg_correct hodd, mulBits_matrixBits, transposeBits_matrixBits]
  apply congrArg List.ofFn
  funext i
  rw [shoupSelfDualBasis_apply]
  exact (shoupChangedVectors_encoding k hk b _ i).symm
end
end MIPRE.SAT

namespace MIPRE.SAT
noncomputable section
open Cost LowDegree LowDegree.BinaryLinear
attribute [local instance] MIPRE.SAT.instFactPrimeOfNatNat_mIPRE_7
theorem shoupSelfDualNormalBasisProg_correct (k : ℕ) (hk : 1 ≤ k) [NeZero k] (hodd : Odd k) :
    shoupSelfDualNormalBasisProg (unary k) =
      List.ofFn (fun i => (shoupBinField k hk).toBits (shoupSelfDualNormalBasis k hk hodd i)) := by
  change shoupSelfDualizeProg (unary k, shoupNormalBasisProg (unary k)) = _
  rw [shoupNormalBasisProg_correct k hk hodd,
    shoupSelfDualizeProg_correct k hk hodd _ (shoupNormalBasis_normal k hk hodd)]
  rfl
end
end MIPRE.SAT

namespace MIPRE.Introspection.BasisProgram
noncomputable section
open Cost Cost.PolyTimeFun SAT LowDegree.BinaryLinear Polynomial
theorem fromBasisProg_correct (k : ℕ) (hk : 1 ≤ k)
    (b : Module.Basis (Fin k) (ZMod 2) (shoupBinField k hk).carrier)
    (a : (shoupBinField k hk).carrier) :
    fromBasisProg (unary k, List.ofFn (fun i => (shoupBinField k hk).toBits (b i)),
      vectorBits (b.equivFun a)) = (shoupBinField k hk).toBits a := by
  change applyBits (transposeBits (unary k).length
    (List.ofFn fun i => (shoupBinField k hk).toBits (b i))) (vectorBits (b.equivFun a)) = _
  rw [length_unary, shoupBasisMatrix_encoding, applyBits_matrixBits,
    shoupBasisMatrix_mulVec, shoupCoordinateEquiv_encoding]
end
end MIPRE.Introspection.BasisProgram

namespace MIPRE.Introspection.BasisProgram
noncomputable section
open Cost Cost.PolyTimeFun SAT LowDegree.BinaryLinear Polynomial
theorem toSelfDualProg_correct (k : ℕ) (hk : 1 ≤ k) [NeZero k] (hodd : Odd k)
    (a : (shoupBinField k hk).carrier) :
    toSelfDualProg (unary k, (shoupBinField k hk).toBits a) =
      vectorBits ((shoupSelfDualNormalBasis k hk hodd).equivFun a) := by
  change shoupInBasisProg (unary k, shoupSelfDualNormalBasisProg (unary k),
    (shoupBinField k hk).toBits a) = _
  rw [shoupSelfDualNormalBasisProg_correct k hk hodd, shoupInBasisProg_correct]
end
end MIPRE.Introspection.BasisProgram

namespace MIPRE.Introspection.BasisProgram
noncomputable section
open Cost Cost.PolyTimeFun SAT LowDegree.BinaryLinear Polynomial
theorem fromSelfDualProg_correct (k : ℕ) (hk : 1 ≤ k) [NeZero k] (hodd : Odd k)
    (a : (shoupBinField k hk).carrier) :
    fromSelfDualProg (unary k,
      vectorBits ((shoupSelfDualNormalBasis k hk hodd).equivFun a)) =
      (shoupBinField k hk).toBits a := by
  change fromBasisProg (unary k, shoupSelfDualNormalBasisProg (unary k),
    vectorBits ((shoupSelfDualNormalBasis k hk hodd).equivFun a)) = _
  rw [shoupSelfDualNormalBasisProg_correct k hk hodd, fromBasisProg_correct]
end
end MIPRE.Introspection.BasisProgram

namespace MIPRE.Introspection.BasisProgram
noncomputable section
open Cost Cost.PolyTimeFun SAT LowDegree.BinaryLinear Polynomial
theorem toSelfDualRowsProg_apply (k : Unary) (vs : List BitStr) :
    toSelfDualRowsProg (k, vs) = vs.map (fun v => toSelfDualProg (k, v)) := rfl
end
end MIPRE.Introspection.BasisProgram

namespace MIPRE.Introspection.BasisProgram
noncomputable section
open Cost Cost.PolyTimeFun SAT LowDegree.BinaryLinear Polynomial
theorem fromSelfDualRowsProg_apply (k : Unary) (vs : List BitStr) :
    fromSelfDualRowsProg (k, vs) = vs.map (fun v => fromSelfDualProg (k, v)) := rfl
end
end MIPRE.Introspection.BasisProgram

namespace MIPRE.Introspection.BasisProgram
noncomputable section
open Cost Cost.PolyTimeFun SAT LowDegree.BinaryLinear Polynomial
theorem toSelfDualRowsProg_correct (k : ℕ) (hk : 1 ≤ k) [NeZero k] (hodd : Odd k)
    {n : ℕ} (u : Fin n → (shoupBinField k hk).carrier) :
    toSelfDualRowsProg (unary k, (shoupBinField k hk).vecBits u) =
      List.ofFn (fun i => vectorBits ((shoupSelfDualNormalBasis k hk hodd).equivFun (u i))) := by
  simp only [toSelfDualRowsProg_apply, BinField.vecBits, List.map_ofFn]
  apply congrArg List.ofFn
  funext i
  exact toSelfDualProg_correct k hk hodd (u i)
end
end MIPRE.Introspection.BasisProgram

namespace MIPRE.Introspection.BasisProgram
noncomputable section
open Cost Cost.PolyTimeFun SAT LowDegree.BinaryLinear Polynomial
theorem fromSelfDualRowsProg_correct (k : ℕ) (hk : 1 ≤ k) [NeZero k] (hodd : Odd k)
    {n : ℕ} (u : Fin n → (shoupBinField k hk).carrier) :
    fromSelfDualRowsProg (unary k,
      List.ofFn (fun i => vectorBits ((shoupSelfDualNormalBasis k hk hodd).equivFun (u i)))) =
      (shoupBinField k hk).vecBits u := by
  simp only [fromSelfDualRowsProg_apply, BinField.vecBits, List.map_ofFn]
  apply congrArg List.ofFn
  funext i
  exact fromSelfDualProg_correct k hk hodd (u i)
end
end MIPRE.Introspection.BasisProgram

namespace MIPRE.Introspection.BinaryBlock
noncomputable section
open Cost Cost.PolyTimeFun Polynomial SAT LowDegree.BinaryLinear BasisProgram
theorem splitBlocks_flatten (k : ℕ) (vs : List BitStr)
    (hv : ∀ v ∈ vs, v.length = k) : splitBlocks vs.length k vs.flatten = vs := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    have hlen := hv v (by simp)
    have ht : (v ++ vs.flatten).take k = v := by rw [← hlen, List.take_left]
    have hd : (v ++ vs.flatten).drop k = vs.flatten := by rw [← hlen, List.drop_left]
    simp only [List.length_cons, splitBlocks, List.flatten_cons, ht, hd]
    rw [ih (fun w hw => hv w (by simp [hw]))]
end
end MIPRE.Introspection.BinaryBlock

namespace MIPRE.Introspection.BinaryBlock
noncomputable section
open Cost Cost.PolyTimeFun Polynomial SAT LowDegree.BinaryLinear BasisProgram
theorem decodeBlocksProg_apply (n k : Unary) (v : BitStr) :
    decodeBlocksProg (n, k, v) = fromSelfDualRowsProg (k, splitBlocks n.length k.length v) := rfl
end
end MIPRE.Introspection.BinaryBlock

namespace MIPRE.Introspection.BinaryBlock
noncomputable section
open Cost Cost.PolyTimeFun Polynomial SAT LowDegree.BinaryLinear BasisProgram
theorem encodeBlocksProg_apply (k : Unary) (vs : List BitStr) :
    encodeBlocksProg (k, vs) = (toSelfDualRowsProg (k, vs)).flatten := rfl
end
end MIPRE.Introspection.BinaryBlock

namespace MIPRE.Introspection.BinaryBlock
noncomputable section
open Cost Cost.PolyTimeFun Polynomial SAT LowDegree.BinaryLinear BasisProgram
theorem encodeBlocksProg_correct (k : ℕ) (hk : 1 ≤ k) [NeZero k] (hodd : Odd k)
    {n : ℕ} (u : Fin n → (shoupBinField k hk).carrier) :
    encodeBlocksProg (unary k, (shoupBinField k hk).vecBits u) =
      (List.ofFn (fun i => vectorBits ((shoupSelfDualNormalBasis k hk hodd).equivFun (u i)))).flatten := by
  rw [encodeBlocksProg_apply, toSelfDualRowsProg_correct k hk hodd]
end
end MIPRE.Introspection.BinaryBlock

namespace MIPRE.Introspection.BinaryBlock
noncomputable section
open Cost Cost.PolyTimeFun Polynomial SAT LowDegree.BinaryLinear BasisProgram
theorem decodeBlocksProg_correct (k : ℕ) (hk : 1 ≤ k) [NeZero k] (hodd : Odd k)
    {n : ℕ} (u : Fin n → (shoupBinField k hk).carrier) :
    decodeBlocksProg (unary n, unary k,
      (List.ofFn (fun i => vectorBits ((shoupSelfDualNormalBasis k hk hodd).equivFun (u i)))).flatten) =
      (shoupBinField k hk).vecBits u := by
  rw [decodeBlocksProg_apply, length_unary, length_unary]
  have he := splitBlocks_flatten k
    (List.ofFn fun i => vectorBits ((shoupSelfDualNormalBasis k hk hodd).equivFun (u i))) (by
      intro v hv
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hv
      simp [vectorBits])
  simp only [List.length_ofFn] at he
  rw [he, fromSelfDualRowsProg_correct k hk hodd]
end
end MIPRE.Introspection.BinaryBlock

namespace MIPRE.LIDT.Adapter
section
open Finset Submodule Module MIPRE.CL
variable {F : Type*} [Field F] {n : ℕ}
/-- Uniqueness of the decomposition along complementary submodules, as a rewriting rule:
an element of `p` congruent to `x` modulo `q` *is* the projection of `x`. This is how
`canonLin` is computed, since `canonLin S` is the projection onto the canonical complement
along `S`. -/
theorem projection_eq_of {E : Type*} [AddCommGroup E] [Module F E] {p q : Submodule F E}
    (hpq : IsCompl p q) {x y : E} (hy : y ∈ p) (hxy : x - y ∈ q) :
    p.projection q hpq x = y := by
  have h1 : (p.projection q hpq x : E) - y ∈ p :=
    Submodule.sub_mem _ (Submodule.projection_apply_mem hpq x) hy
  have h2 : (p.projection q hpq x : E) - y ∈ q := by
    have e : (p.projection q hpq x : E) - y = -(x - (p.projection q hpq x : E)) + (x - y) := by
      abel
    rw [e]
    exact Submodule.add_mem _ (Submodule.neg_mem _ (Submodule.sub_projection_mem hpq x)) hxy
  have hbot := hpq.inf_eq_bot
  rw [Submodule.eq_bot_iff] at hbot
  exact sub_eq_zero.mp (hbot _ ⟨h1, h2⟩)
end
end MIPRE.LIDT.Adapter

namespace MIPRE.LIDT.Adapter
section
open Finset Submodule Module MIPRE.CL
variable {F : Type*} [Field F] {n : ℕ}
/-- The seeded test's canonical base point for an axis-parallel direction: `rep eᵢ u`
zeroes the `i`-th coordinate of `u`. -/
theorem rep_single (i : Fin n) (u : Fin n → F) :
    canonLin (span F {(Pi.single i 1 : Fin n → F)}) u
      = u - u i • (Pi.single i 1 : Fin n → F) := by
  classical
  refine projection_eq_of
    (isCompl_canonCompl (span F {(Pi.single i 1 : Fin n → F)})).symm ?_ ?_
  · rw [canonCompl, mem_coordSub]
    intro j hj
    rw [pivots_line, Finset.mem_singleton] at hj
    subst hj
    simp
  · rw [sub_sub_cancel]
    exact Submodule.mem_span_singleton.mpr ⟨u i, rfl⟩
end
end MIPRE.LIDT.Adapter

namespace MIPRE.QLD.PauliCL
noncomputable section
open Introspection.SeedProgram Introspection.SeededLineProgram SAT
theorem axisRepresentativeProg_canonLin (k : ℕ) (hk : 1 ≤ k) (j : ℕ) (hj : j ≤ k)
    (s : (shoupBinField k hk).carrier)
    (u : Fin (2 ^ j) → (shoupBinField k hk).carrier) :
    axisRepresentativeProg ((Cost.unary k, Cost.unary j, (shoupBinField k hk).toBits s),
      (shoupBinField k hk).vecBits u) =
      (shoupBinField k hk).vecBits (CL.canonLin (Submodule.span
        (shoupBinField k hk).carrier {Pi.single (selector (shoupBinField k hk) j hj s) 1}) u) := by
  rw [axisRepresentativeProg_correct k hk j hj s u, LIDT.Adapter.rep_single]
  apply congrArg (shoupBinField k hk).vecBits
  funext i
  by_cases hi : i = selector (shoupBinField k hk) j hj s
  · simp [hi]
  · simp [hi]
end
end MIPRE.QLD.PauliCL

namespace MIPRE.QLD.PauliCL
noncomputable section
open Cost SAT Introspection.PauliStageProgram Introspection.SeedProgram
open Introspection.SeededLineProgram Introspection.LineProgram
theorem stageOne_correct (k : ℕ) (hk : 1 ≤ k) (j : ℕ) (T : Ty)
    (u x : Coord (2 ^ j) → (shoupBinField k hk).carrier) :
    stageOne (stageInput k hk j T u x) =
      fieldEncoding (shoupBinField k hk) (seedMap T x) := by
  cases T <;> (try cases ‹Bas›) <;>
    simp only [fieldEncoding, seedMap, CL.RegLinear.id_apply, CL.RegLinear.zero_apply]
  all_goals
    simp [stageOne, pack, isKind, kind, zeroPoint, zeroField, dimension, fieldWidth,
      seed, vector, stageInput, programTag, fieldEncoding, shoupZeroProg_correct k hk,
      CL.proj_apply, seedSet, BinField.vecBits, Function.comp_def]
end
end MIPRE.QLD.PauliCL

namespace MIPRE.QLD.PauliCL
noncomputable section
open Cost SAT Introspection.PauliStageProgram Introspection.SeedProgram
open Introspection.SeededLineProgram Introspection.LineProgram
theorem stageTwo_correct (k : ℕ) (hk : 1 ≤ k) (j : ℕ) (hj : j ≤ k) (T : Ty)
    (u x : Coord (2 ^ j) → (shoupBinField k hk).carrier) :
    stageTwo (stageInput k hk j T u x) =
      fieldEncoding (shoupBinField k hk)
        (ExplicitSeed.secondMap (selector (shoupBinField k hk) j hj) T (u .seed) x) := by
  cases T <;> (try cases ‹Bas›) <;>
    simp only [fieldEncoding, ExplicitSeed.secondMap, directionMap_apply, CL.RegLinear.zero_apply]
  all_goals
    simp [stageTwo, pack, isKind, kind, zeroPoint, zeroField, dimension, fieldWidth,
      seed, vector, prefixData, direction, selectorWidth, stageInput, programTag,
      fieldEncoding, shoupZeroProg_correct k hk, selectedDirectionProg_correct k hk j hj]
  all_goals simp [BinField.vecBits]
end
end MIPRE.QLD.PauliCL

namespace MIPRE.QLD.PauliCL
noncomputable section
open Cost SAT Introspection.PauliStageProgram Introspection.SeedProgram
open Introspection.SeededLineProgram Introspection.LineProgram
theorem stageThree_correct (k : ℕ) (hk : 1 ≤ k) (j : ℕ) (hj : j ≤ k) (T : Ty)
    (u x : Coord (2 ^ j) → (shoupBinField k hk).carrier) :
    stageThree (stageInput k hk j T u x) =
      fieldEncoding (shoupBinField k hk)
        (ExplicitSeed.finalMap (selector (shoupBinField k hk) j hj) T
          (u .seed) (fun i => u (.direction i)) x) := by
  cases T <;> (try cases ‹Bas›) <;>
    simp only [fieldEncoding, ExplicitSeed.finalMap, pointMap_apply,
      CL.RegLinear.id_apply, CL.RegLinear.zero_apply]
  all_goals
    simp [stageThree, pointFields, fullFields, zeros, pack, isKind, kind, zeroPoint,
      zeroField, dimension, fieldWidth, seed, vector, prefixData, direction, selectorWidth,
      basis, finalPoint, selectedPoint, pointX, pointZ, scalarX, scalarZ,
      stageInput, programTag, fieldEncoding, shoupZeroProg_correct k hk,
      axisRepresentativeProg_canonLin k hk j hj, lineRepresentativeProg_correct k hk,
      representative_eq_canonLin]
  all_goals simp [finalSet, seedSet, directionSet, BinField.vecBits,
    Function.comp_def]
end
end MIPRE.QLD.PauliCL

namespace MIPRE.QLD.PauliCL
noncomputable section
open Cost SAT Introspection.PauliStageProgram Introspection.SeedProgram
open Introspection.SeededLineProgram Introspection.LineProgram
variable {F : Type*} [Field F] {m : ℕ}
theorem presentation_mapOfPrefix_one (χ : F → Fin m) (T : Ty) (u x : Coord m → F) :
    (ExplicitSeed.presentation χ T).mapOfPrefix 0 u x = seedMap T x := rfl
end
end MIPRE.QLD.PauliCL

namespace MIPRE.QLD.PauliCL
noncomputable section
open Cost SAT Introspection.PauliStageProgram Introspection.SeedProgram
open Introspection.SeededLineProgram Introspection.LineProgram
variable {F : Type*} [Field F] {m : ℕ}
theorem presentation_mapOfPrefix_two (χ : F → Fin m) (T : Ty) (u x : Coord m → F) :
    (ExplicitSeed.presentation χ T).mapOfPrefix 1 u x =
      ExplicitSeed.secondMap χ T (u .seed) x := by
  change ExplicitSeed.secondMap χ T (CL.proj (seedSet m) u .seed) x = _
  have hs : CL.proj (seedSet m) u .seed = u .seed := by simp [CL.proj_apply, seedSet]
  rw [hs]
end
end MIPRE.QLD.PauliCL

namespace MIPRE.QLD.PauliCL
noncomputable section
open Cost SAT Introspection.PauliStageProgram Introspection.SeedProgram
open Introspection.SeededLineProgram Introspection.LineProgram
variable {F : Type*} [Field F] {m : ℕ}
theorem presentation_mapOfPrefix_three (χ : F → Fin m) (T : Ty) (u x : Coord m → F) :
    (ExplicitSeed.presentation χ T).mapOfPrefix 2 u x =
      ExplicitSeed.finalMap χ T (u .seed) (fun i => u (.direction i)) x := by
  change ExplicitSeed.finalMap χ T (CL.proj (seedSet m) u .seed)
    (fun i => CL.proj (directionSet m) (CL.proj (seedSet m)ᶜ u) (.direction i)) x = _
  have hs : CL.proj (seedSet m) u .seed = u .seed := by simp [CL.proj_apply, seedSet]
  have hd : (fun i => CL.proj (directionSet m) (CL.proj (seedSet m)ᶜ u) (.direction i)) =
      (fun i => u (.direction i)) := by
    funext i
    simp [CL.proj_apply, seedSet, directionSet]
  rw [hs, hd]
end
end MIPRE.QLD.PauliCL

namespace MIPRE.QLD.PauliCL
noncomputable section
open Cost SAT Introspection.PauliStageProgram Introspection.SeedProgram
open Introspection.SeededLineProgram Introspection.LineProgram
/-- The linear-query compiler is correct on every prefix, including prefixes
that are not attained by the preceding stages. -/
theorem linear_correct (k : ℕ) (hk : 1 ≤ k) (j : ℕ) (hj : j ≤ k) (T : Ty)
    (r : ℕ) (hr1 : 1 ≤ r) (hr3 : r ≤ 3)
    (u x : Coord (2 ^ j) → (shoupBinField k hk).carrier) :
    linear (r, stageInput k hk j T u x) =
      fieldEncoding (shoupBinField k hk)
        ((ExplicitSeed.presentation (selector (shoupBinField k hk) j hj) T).mapOfPrefix
          (r - 1) u x) := by
  interval_cases r
  · rw [linear_one, show 1 - 1 = 0 by rfl, presentation_mapOfPrefix_one]
    exact stageOne_correct k hk j T u x
  · rw [linear_two, show 2 - 1 = 1 by rfl, presentation_mapOfPrefix_two]
    exact stageTwo_correct k hk j hj T u x
  · rw [linear_three, show 3 - 1 = 2 by rfl, presentation_mapOfPrefix_three]
    exact stageThree_correct k hk j hj T u x
end
end MIPRE.QLD.PauliCL

namespace MIPRE.QLD.PauliCL
noncomputable section
open Cost SAT LowDegree.BinaryLinear Introspection.BinaryBlock
set_option linter.unusedSectionVars false
theorem numberedRows_length {k m : ℕ} (E : BinField k) (x : Coord m → E.carrier) :
    (numberedRows E x).length = 3 * m + 3 := List.length_ofFn
end
end MIPRE.QLD.PauliCL

namespace MIPRE.QLD.PauliCL
noncomputable section
open Cost SAT LowDegree.BinaryLinear Introspection.BinaryBlock
set_option linter.unusedSectionVars false
theorem numberedRows_getD {k m : ℕ} (E : BinField k) (x : Coord m → E.carrier)
    (c : Coord m) :
    (numberedRows E x).getD (coordNumbering m c).val [] = E.toBits (x c) := by
  simp only [numberedRows, List.getD_eq_getElem?_getD, List.getElem?_ofFn,
    (coordNumbering m c).isLt, dite_true, Option.getD_some, Fin.eta,
    Equiv.symm_apply_apply]
end
end MIPRE.QLD.PauliCL

namespace MIPRE.QLD.PauliCL
noncomputable section
open Cost SAT LowDegree.BinaryLinear Introspection.BinaryBlock
set_option linter.unusedSectionVars false
theorem numberedRows_eq_vecBits {k m : ℕ} (E : BinField k) (x : Coord m → E.carrier) :
    numberedRows E x = E.vecBits (fun i => x ((coordNumbering m).symm i)) := by
  simp only [numberedRows, BinField.vecBits, List.map_ofFn, Function.comp_def]
end
end MIPRE.QLD.PauliCL

namespace MIPRE.QLD.PauliCL
noncomputable section
open Cost SAT LowDegree.BinaryLinear Introspection.BinaryBlock
set_option linter.unusedSectionVars false
/-- The executable encoder produces the exact numbered CL bit vector. -/
theorem encodeBlocksProg_numberedRows (k : ℕ) (hk : 1 ≤ k) [NeZero k] (hodd : Odd k)
    {m : ℕ} [NeZero m] (x : Coord m → (shoupBinField k hk).carrier) :
    encodeBlocksProg (unary k, numberedRows (shoupBinField k hk) x) =
      CL.toBits (binaryVectorEquiv (shoupSelfDualNormalBasis k hk hodd) x) := by
  rw [numberedRows_eq_vecBits, encodeBlocksProg_correct k hk hodd, binaryVectorEquiv_bits]
end
end MIPRE.QLD.PauliCL

namespace MIPRE.QLD.PauliCL
noncomputable section
open Cost SAT LowDegree.BinaryLinear Introspection.BinaryBlock
set_option linter.unusedSectionVars false
/-- The executable decoder returns the exact canonical field row at each
numbered coordinate of the self-dual downsized vector. -/
theorem decodeBlocksProg_binaryVector (k : ℕ) (hk : 1 ≤ k) [NeZero k] (hodd : Odd k)
    {m : ℕ} [NeZero m] (x : Coord m → (shoupBinField k hk).carrier) :
    decodeBlocksProg (unary (3 * m + 3), unary k,
      CL.toBits (binaryVectorEquiv (shoupSelfDualNormalBasis k hk hodd) x)) =
      numberedRows (shoupBinField k hk) x := by
  rw [binaryVectorEquiv_bits, decodeBlocksProg_correct k hk hodd, numberedRows_eq_vecBits]
end
end MIPRE.QLD.PauliCL

namespace MIPRE.Introspection.PauliStageProgram
noncomputable section
open Cost Cost.PolyTimeFun
theorem unpackRows_packRows (m : ℕ) (x z : List BitStr) (s : BitStr)
    (v : List BitStr) (rx rz : BitStr)
    (hx : x.length = m) (hz : z.length = m) (hv : v.length = m) :
    unpackRows (unary m, packRows (x, z, s, v, rx, rz)) = (x, z, s, v, rx, rz) := by
  simp [unpackRows, pack, hx, hz, hv]
end
end MIPRE.Introspection.PauliStageProgram

namespace MIPRE.QLD.PauliCL
noncomputable section
open Cost SAT Introspection.PauliStageProgram
theorem packRows_fieldEncoding_getD {k m : ℕ} (E : BinField k)
    (x : Coord m → E.carrier) (c : Coord m) :
    (packRows (fieldEncoding E x)).getD (coordNumbering m c).val [] = E.toBits (x c) := by
  have hlen (v : Fin m → E.carrier) : (E.vecBits v).length = m := by simp [BinField.vecBits]
  have hget (v : Fin m → E.carrier) (i : Fin m) :
      (E.vecBits v).getD i.val [] = E.toBits (v i) := by
    simp [BinField.vecBits, List.getD_eq_getElem?_getD, i.isLt]
  cases c with
  | point W i =>
    cases W with
    | X =>
      simp only [fieldEncoding, packRows_apply, coordNumbering_point_X]
      rw [List.getD_append _ _ _ _ (by simpa only [hlen] using i.isLt), hget]
    | Z =>
      simp only [fieldEncoding, packRows_apply, coordNumbering_point_Z]
      rw [List.getD_append_right _ _ _ _ (by simp only [hlen]; omega), hlen,
        Nat.add_sub_cancel_left, List.getD_append _ _ _ _ (by simpa only [hlen] using i.isLt), hget]
  | seed =>
    simp only [fieldEncoding, packRows_apply, coordNumbering_seed]
    rw [List.getD_append_right _ _ _ _ (by simp only [hlen]; omega), hlen,
      List.getD_append_right _ _ _ _ (by simp only [hlen]; omega), hlen]
    simp [show 2 * m - m - m = 0 by omega]
  | direction i =>
    simp only [fieldEncoding, packRows_apply, coordNumbering_direction]
    rw [List.getD_append_right _ _ _ _ (by simp only [hlen]; omega), hlen,
      List.getD_append_right _ _ _ _ (by simp only [hlen]; omega), hlen]
    rw [show 2 * m + 1 + i.val - m - m = i.val + 1 by omega]
    simp only [List.getD_cons_succ]
    rw [List.getD_append _ _ _ _ (by simpa only [hlen] using i.isLt), hget]
  | scalar W =>
    cases W <;> simp only [fieldEncoding, packRows_apply,
      coordNumbering_scalar_X, coordNumbering_scalar_Z]
    all_goals
      rw [List.getD_append_right _ _ _ _ (by simp only [hlen]; omega), hlen,
        List.getD_append_right _ _ _ _ (by simp only [hlen]; omega), hlen]
    · rw [show 3 * m + 1 - m - m = m + 1 by omega]
      simp only [List.getD_cons_succ]
      rw [List.getD_append_right _ _ _ _ (by simp [hlen]), hlen]
      simp
    · rw [show 3 * m + 2 - m - m = (m + 1) + 1 by omega]
      simp only [List.getD_cons_succ]
      rw [List.getD_append_right _ _ _ _ (by simp only [hlen]; omega), hlen]
      simp
end
end MIPRE.QLD.PauliCL

namespace MIPRE.QLD.PauliCL
noncomputable section
open Cost SAT Introspection.PauliStageProgram
theorem packRows_fieldEncoding {k m : ℕ} (E : BinField k)
    (x : Coord m → E.carrier) : packRows (fieldEncoding E x) = numberedRows E x := by
  have hlen : (packRows (fieldEncoding E x)).length = 3 * m + 3 := by
    simp [packRows, fieldEncoding, pointX, pointZ, seed, direction, scalarX, scalarZ,
      BinField.vecBits]
    omega
  apply List.ext_getElem
  · rw [hlen, numberedRows_length]
  · intro i hi hi'
    have hil : i < 3 * m + 3 := by simpa only [hlen] using hi
    let c := (coordNumbering m).symm ⟨i, hil⟩
    have hc : (coordNumbering m c).val = i := by simp [c]
    have he := (packRows_fieldEncoding_getD E x c).trans (numberedRows_getD E x c).symm
    simpa only [hc, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi,
      List.getElem?_eq_getElem hi', Option.getD_some] using he
end
end MIPRE.QLD.PauliCL

namespace MIPRE.QLD.PauliCL
noncomputable section
open Cost SAT Introspection.PauliStageProgram
theorem unpackRows_numberedRows {k m : ℕ} (E : BinField k)
    (x : Coord m → E.carrier) : unpackRows (unary m, numberedRows E x) = fieldEncoding E x := by
  rw [← packRows_fieldEncoding]
  exact unpackRows_packRows m _ _ _ _ _ _ (by simp [BinField.vecBits])
    (by simp [BinField.vecBits]) (by simp [BinField.vecBits])
end
end MIPRE.QLD.PauliCL

namespace MIPRE.QLD.PauliCL
noncomputable section
open Cost SAT Introspection.PauliStageProgram
theorem rowInput_correct (k : ℕ) (hk : 1 ≤ k) (j : ℕ) (T : Ty) (r : ℕ)
    (u x : Coord (2 ^ j) → (shoupBinField k hk).carrier) :
    rowInput ((unary k, unary j, unary (2 ^ j)), programTag T, r,
      numberedRows (shoupBinField k hk) u, numberedRows (shoupBinField k hk) x) =
      stageInput k hk j T u x := by
  simp only [rowInput, PolyTimeFun.pair_apply, PolyTimeFun.comp_apply,
    PolyTimeFun.ap₂_apply, PolyTimeFun.fst_apply, PolyTimeFun.snd_apply,
    unpackRows_numberedRows, stageInput]
end
end MIPRE.QLD.PauliCL

namespace MIPRE.QLD.PauliCL
noncomputable section
open Cost SAT Introspection.PauliStageProgram
theorem linearRows_correct (k : ℕ) (hk : 1 ≤ k) (j : ℕ) (hj : j ≤ k)
    (T : Ty) (r : ℕ) (hr1 : 1 ≤ r) (hr3 : r ≤ 3)
    (u x : Coord (2 ^ j) → (shoupBinField k hk).carrier) :
    linearRows ((unary k, unary j, unary (2 ^ j)), programTag T, r,
      numberedRows (shoupBinField k hk) u, numberedRows (shoupBinField k hk) x) =
      numberedRows (shoupBinField k hk)
        ((ExplicitSeed.presentation (Introspection.SeedProgram.selector
          (shoupBinField k hk) j hj) T).mapOfPrefix (r - 1) u x) := by
  change packRows (linear (r, rowInput _)) = _
  rw [rowInput_correct, linear_correct k hk j hj T r hr1 hr3, packRows_fieldEncoding]
end
end MIPRE.QLD.PauliCL

namespace MIPRE.QLD.PauliCL
noncomputable section
open Cost SAT Introspection.PauliStageProgram
theorem binaryInput_correct (k : ℕ) (hk : 1 ≤ k) [NeZero k] (hodd : Odd k)
    (j : ℕ) (T : Ty) (r : ℕ)
    (u x : Coord (2 ^ j) → (shoupBinField k hk).carrier) :
    binaryInput ((unary k, unary j, unary (2 ^ j)), programTag T, r,
      CL.toBits (binaryVectorEquiv (shoupSelfDualNormalBasis k hk hodd) u),
      CL.toBits (binaryVectorEquiv (shoupSelfDualNormalBasis k hk hodd) x)) =
      ((unary k, unary j, unary (2 ^ j)), programTag T, r,
        numberedRows (shoupBinField k hk) u, numberedRows (shoupBinField k hk) x) := by
  have hc (m : ℕ) : unary m ++ (unary m ++ (unary m ++ unary 3)) = unary (3 * m + 3) := by
    simp only [unary, ← List.replicate_add]
    congr 1
    omega
  simp only [binaryInput, PolyTimeFun.comp_apply, PolyTimeFun.pair_apply,
    PolyTimeFun.ap₂_apply, PolyTimeFun.append_apply, PolyTimeFun.fst_apply,
    PolyTimeFun.snd_apply, PolyTimeFun.const_apply, hc, decodeBlocksProg_binaryVector k hk hodd]
end
end MIPRE.QLD.PauliCL

namespace MIPRE.QLD.PauliCL
noncomputable section
open Cost SAT Introspection.PauliStageProgram
theorem binaryPresentation_mapOfPrefix {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    [Algebra (ZMod 2) F] {m k : ℕ} [NeZero m]
    (χ : F → Fin m) (b : Module.Basis (Fin k) (ZMod 2) F) (T : Ty)
    (r : ℕ) (u x : Coord m → F) :
    (ExplicitSeed.binaryPresentation χ b T).mapOfPrefix r
      (binaryVectorEquiv b u) (binaryVectorEquiv b x) =
      binaryVectorEquiv b ((ExplicitSeed.presentation χ T).mapOfPrefix r u x) := by
  change (((ExplicitSeed.presentation χ T).downsize b).reindex (binaryCoordEquiv m k)).mapOfPrefix r
    (CL.reindexEquiv (binaryCoordEquiv m k) (CL.downsizeEquiv b u))
    (CL.reindexEquiv (binaryCoordEquiv m k) (CL.downsizeEquiv b x)) = _
  rw [CL.CLFun.mapOfPrefix_reindex, CL.CLFun.mapOfPrefix_downsize]
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
    LinearMap.restrictScalars_apply]
  rfl
end
end MIPRE.QLD.PauliCL

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.QLD.PauliCL
open Cost SAT Introspection.PauliStageProgram
theorem _root_.solution (k : ℕ) (hk : 1 ≤ k) [NeZero k] (hodd : Odd k)
    (j : ℕ) (hj : j ≤ k) (T : Ty) (r : ℕ) (hr1 : 1 ≤ r) (hr3 : r ≤ 3)
    (u x : Coord (2 ^ j) → (shoupBinField k hk).carrier) :
    linearBits ((unary k, unary j, unary (2 ^ j)), programTag T, r,
      CL.toBits (binaryVectorEquiv (shoupSelfDualNormalBasis k hk hodd) u),
      CL.toBits (binaryVectorEquiv (shoupSelfDualNormalBasis k hk hodd) x)) =
      CL.toBits ((ExplicitSeed.binaryPresentation
        (Introspection.SeedProgram.selector (shoupBinField k hk) j hj)
        (shoupSelfDualNormalBasis k hk hodd) T).mapOfPrefix (r - 1)
        (binaryVectorEquiv (shoupSelfDualNormalBasis k hk hodd) u)
        (binaryVectorEquiv (shoupSelfDualNormalBasis k hk hodd) x)) := by
  change Introspection.BinaryBlock.encodeBlocksProg (unary k, linearRows (binaryInput _)) = _
  rw [binaryInput_correct k hk hodd, linearRows_correct k hk j hj T r hr1 hr3,
    encodeBlocksProg_numberedRows k hk hodd, binaryPresentation_mapOfPrefix]
end MIPRE.QLD.PauliCL
