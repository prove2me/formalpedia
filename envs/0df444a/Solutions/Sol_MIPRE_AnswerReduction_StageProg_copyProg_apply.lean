-- Prove2me | solution 1 for MIPRE.AnswerReduction.StageProg.copyProg_apply
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T05:55:33.846893+00:00
-- url     : https://prove2.me/submissions/f28d6a6b-ff30-43a5-bf7d-7f452ade523d

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/AnswerReduction/StageProg.lean (solution of MIPRE.AnswerReduction.StageProg.copyProg_apply);
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
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Image
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
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
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
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Background_LIDT_Game
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Canonical
import Definitions.Def_MIPRE_Background_LIDT_CLGame
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Background_LIDT_Presentation
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
import Definitions.Def_MIPRE_Background_AnswerReduction_PcpPresentation
import Definitions.Def_MIPRE_Foundations_CL_Embedding
import Definitions.Def_MIPRE_Foundations_CL_Product
import Definitions.Def_MIPRE_Foundations_CL_Downsize
import Definitions.Def_MIPRE_Foundations_CL_TypedSampler
import Definitions.Def_MIPRE_Foundations_CL_ProductSampler
import Definitions.Def_MIPRE_Background_LIDT_PresentationQueries
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
import Definitions.Def_MIPRE_Background_AnswerReduction_Layout
import Definitions.Def_MIPRE_Background_AnswerReduction_Stages
import Definitions.Def_MIPRE_Background_AnswerReduction_StageLists
import Definitions.Def_MIPRE_Foundations_Cost_BinaryArithmetic
import Definitions.Def_MIPRE_Foundations_Introspection_SeedSelectorProg
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryFold
import Definitions.Def_MIPRE_Foundations_SAT_NormalElementProg
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryInverse
import Definitions.Def_MIPRE_Foundations_Introspection_LineRepresentativeProg
import Definitions.Def_MIPRE_Foundations_Cost_BinaryCompare
import Definitions.Def_MIPRE_Foundations_Introspection_SeededLineProg
import Definitions.Def_MIPRE_Foundations_Cost_TreeBits
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgFinite
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgParse
import Definitions.Def_MIPRE_Foundations_Introspection_BinaryBlockProg
import Definitions.Def_MIPRE_Background_AnswerReduction_StageProg
import Theorems.Thm_MIPRE_Introspection_BinaryBlock_splitBlocksProg_apply

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.AnswerReduction.StageProg
noncomputable section
open Cost Cost.PolyTimeFun Pcp Introspection.SeededLineProgram Introspection.LineProgram
variable (x : Input)
theorem blocksP_apply (z : PolyTimeFun Input BitStr) :
    blocksP z x = blocksOf (kI x) (mI x) (z x) := by
  simp only [blocksP, blocksOf, pair_apply, comp_apply, take_apply, drop_apply, ap₂_apply,
    append_apply, const_apply, Introspection.BinaryBlock.splitBlocksProg_apply,
    List.length_append, length_unary]
end
end MIPRE.AnswerReduction.StageProg

namespace MIPRE.AnswerReduction.StageProg
noncomputable section
open Cost Cost.PolyTimeFun Pcp Introspection.SeededLineProgram Introspection.LineProgram
variable (x : Input)
theorem ptMapP_apply (s : PolyTimeFun Input BitStr) (dir w : PolyTimeFun Input (List BitStr)) :
    ptMapP s dir w x = ptMapL (kI x) (dI x) (τI x) (s x) (dir x) (w x) := by
  simp only [ptMapP, ptMapL, PolyTimeFun.ite_apply, isτ, ap₂_apply, SAT.ArrayProg.eqNat_apply,
    const_apply, decide_eq_true_eq, comp_apply, pair_apply]
  rfl
end
end MIPRE.AnswerReduction.StageProg

namespace MIPRE.AnswerReduction.StageProg
noncomputable section
open Cost Cost.PolyTimeFun Pcp Introspection.SeededLineProgram Introspection.LineProgram
variable (x : Input)
theorem seedOutP_apply (s : PolyTimeFun Input BitStr) (seeds : PolyTimeFun Input (List BitStr)) :
    seedOutP s seeds x = seedOut (kI x) (dI x) (τI x) (s x) (seeds x) := by
  simp only [seedOutP, seedOut, PolyTimeFun.ite_apply, isτ, ap₂_apply,
    SAT.ArrayProg.eqNat_apply, const_apply, decide_eq_true_eq, comp_apply, pair_apply,
    cons_apply]
  split_ifs
  · rfl
  · exact placeP_apply _ _ _ _
end
end MIPRE.AnswerReduction.StageProg

namespace MIPRE.AnswerReduction.StageProg
noncomputable section
open Cost Cost.PolyTimeFun Pcp Introspection.SeededLineProgram Introspection.LineProgram
variable (x : Input)
theorem dirOutP_apply (s : PolyTimeFun Input BitStr) (dirs : PolyTimeFun Input (List BitStr)) :
    dirOutP s dirs x = dirOut (kI x) (dI x) (τI x) (s x) (dirs x) := by
  simp only [dirOutP, dirOut, PolyTimeFun.ite_apply, isτ, ap₂_apply,
    SAT.ArrayProg.eqNat_apply, const_apply, decide_eq_true_eq, comp_apply, pair_apply]
  split_ifs
  · exact placeP_apply _ _ _ _
  · rfl
end
end MIPRE.AnswerReduction.StageProg

namespace MIPRE.AnswerReduction.StageProg
noncomputable section
open Cost Cost.PolyTimeFun Pcp Introspection.SeededLineProgram Introspection.LineProgram
variable (x : Input)
theorem ptOutP_apply (s : PolyTimeFun Input BitStr) (dir pts : PolyTimeFun Input (List BitStr)) :
    ptOutP s dir pts x = ptOut (kI x) (dI x) (τI x) (s x) (dir x) (pts x) := by
  simp only [ptOutP, ptOut, comp_apply, pair_apply, ptMapP_apply]
  exact placeP_apply _ _ _ _
end
end MIPRE.AnswerReduction.StageProg

namespace MIPRE.AnswerReduction.StageProg
noncomputable section
open Cost Cost.PolyTimeFun Pcp Introspection.SeededLineProgram Introspection.LineProgram
variable (x : Input)
theorem margP_apply (X : PolyTimeFun Input Blocks) :
    margP X x = margL (kI x) (dI x) (τI x) (jI x) (X x) := by
  simp only [margP, margL, pair_apply, PolyTimeFun.ite_apply, ap₂_apply, leNat_apply,
    const_apply, decide_eq_true_eq, ptOutP_apply, dirOutP_apply, seedOutP_apply, comp_apply]
  rfl
end
end MIPRE.AnswerReduction.StageProg

namespace MIPRE.AnswerReduction.StageProg
noncomputable section
open Cost Cost.PolyTimeFun Pcp Introspection.SeededLineProgram Introspection.LineProgram
variable (x : Input)
theorem linP_apply (U Y : PolyTimeFun Input Blocks) :
    linP U Y x = linL (kI x) (dI x) (τI x) (jI x) (U x) (Y x) := by
  simp only [linP, linL, pair_apply, PolyTimeFun.ite_apply, isJ, ap₂_apply,
    SAT.ArrayProg.eqNat_apply, const_apply, decide_eq_true_eq, ptOutP_apply, dirOutP_apply,
    seedOutP_apply, comp_apply]
  rfl
end
end MIPRE.AnswerReduction.StageProg

namespace MIPRE.AnswerReduction.StageProg
noncomputable section
open Cost Cost.PolyTimeFun Pcp Introspection.SeededLineProgram Introspection.LineProgram
variable (x : Input)
theorem facP_apply (U : PolyTimeFun Input Blocks) :
    facP U x = facL (kI x) (dI x) (jI x) (U x) := by
  simp only [facP, facL, pair_apply, PolyTimeFun.ite_apply, isJ, ap₂_apply,
    SAT.ArrayProg.eqNat_apply, const_apply, decide_eq_true_eq, comp_apply, cons_apply,
    placeP_apply, replicate_apply]
  rfl
end
end MIPRE.AnswerReduction.StageProg

namespace MIPRE.AnswerReduction.StageProg
noncomputable section
open Cost Cost.PolyTimeFun Pcp Introspection.SeededLineProgram Introspection.LineProgram
variable (x : Input)
theorem bitsP_apply (X : PolyTimeFun Input Blocks) : bitsP X x = bitsOf (X x) := rfl
end
end MIPRE.AnswerReduction.StageProg

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.AnswerReduction.StageProg
open Cost Cost.PolyTimeFun Pcp Introspection.SeededLineProgram Introspection.LineProgram
theorem _root_.solution (k : Unary) (d : Desc) (τ : ℕ) (m' : Unary) (kind j : ℕ) (u y : BitStr) :
    copyProg (k, d, τ, m', kind, j, u, y) = copyAnswer k d τ m' kind j u y := by
  simp only [copyProg, copyAnswer, PolyTimeFun.ite_apply, isKind, ap₂_apply,
    SAT.ArrayProg.eqNat_apply, kindI, comp_apply, fst_apply, snd_apply, const_apply,
    decide_eq_true_eq, bitsP_apply, margP_apply, linP_apply, facP_apply, blocksP_apply]
  rfl
end MIPRE.AnswerReduction.StageProg
