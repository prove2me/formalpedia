-- Prove2me | solution 1 for MIPRE.AnswerReduction.sideB_eq
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T06:29:44.671228+00:00
-- url     : https://prove2.me/submissions/79a1636c-051f-41dd-804f-e5b923c0c05e

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/AnswerReduction/DecideSpec.lean (solution of MIPRE.AnswerReduction.sideB_eq);
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
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Computability.Primrec.List
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
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Pi
import Mathlib.Logic.Denumerable
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Function.Iterate
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.Polynomial.Content
import Mathlib.RingTheory.Polynomial.Cyclotomic.Factorization
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.IntervalCases
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
import Definitions.Def_MIPRE_Foundations_OracularGame
import Definitions.Def_MIPRE_Background_AnswerReduction_Predicate
import Definitions.Def_MIPRE_Foundations_Closeness
import Definitions.Def_MIPRE_Foundations_PerfectStrategy
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_Foundations_GameDouble
import Definitions.Def_MIPRE_Foundations_OracularSound
import Definitions.Def_MIPRE_Foundations_OpBound
import Definitions.Def_MIPRE_Foundations_StateDistance
import Definitions.Def_MIPRE_Foundations_POVMValue
import Definitions.Def_MIPRE_Foundations_CrossConsistency
import Definitions.Def_MIPRE_Foundations_PVM
import Definitions.Def_MIPRE_Foundations_Commutation
import Definitions.Def_MIPRE_Foundations_Dilation
import Definitions.Def_MIPRE_Foundations_LowDegree_SchwartzZippel
import Definitions.Def_MIPRE_Foundations_Sandwich
import Definitions.Def_MIPRE_Foundations_POVMMix
import Definitions.Def_MIPRE_Foundations_GameAdapt
import Definitions.Def_MIPRE_Foundations_RegisterReindex
import Definitions.Def_MIPRE_Foundations_OracularTensor
import Definitions.Def_MIPRE_Foundations_OracularComplete
import Definitions.Def_MIPRE_Foundations_CL_Embedding
import Definitions.Def_MIPRE_Foundations_CL_Graph
import Definitions.Def_MIPRE_Foundations_CL_Detyping
import Definitions.Def_MIPRE_Foundations_CL_DetypingLaw
import Definitions.Def_MIPRE_Foundations_SampledGame
import Definitions.Def_MIPRE_Foundations_CL_DetypingGame
import Definitions.Def_MIPRE_Foundations_GapCompression
import Definitions.Def_MIPRE_Foundations_Cost_Codable_B
import Definitions.Def_MIPRE_Foundations_Halting_Descriptions
import Definitions.Def_MIPRE_Foundations_OracularTyped
import Definitions.Def_MIPRE_Background_AnswerReduction_AnswerFormat
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
import Definitions.Def_MIPRE_Background_AnswerReduction_Family
import Definitions.Def_MIPRE_Background_AnswerReduction_TypedGame
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
import Definitions.Def_MIPRE_Background_LIDT_Adapter_Geometry
import Definitions.Def_MIPRE_Background_AnswerReduction_StageCorrect
import Definitions.Def_MIPRE_Foundations_CL_DetypingQueries
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgBits
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgCall
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgRoute
import Definitions.Def_MIPRE_Foundations_Cost_Machine_B
import Definitions.Def_MIPRE_Foundations_Cost_MachineData_B
import Definitions.Def_MIPRE_Foundations_Cost_Interpreter_B
import Definitions.Def_MIPRE_Foundations_Cost_MachineBound_B
import Definitions.Def_MIPRE_Foundations_Cost_Toolkit_B
import Definitions.Def_MIPRE_Foundations_Cost_Universal_B
import Definitions.Def_MIPRE_Foundations_CL_ProductSamplerProg
import Definitions.Def_MIPRE_Foundations_Cost_FiniteEncoding
import Definitions.Def_MIPRE_Background_AnswerReduction_PcpSampler
import Definitions.Def_MIPRE_Foundations_Introspection_FieldPolynomialProg
import Definitions.Def_MIPRE_Foundations_Introspection_FieldLineCheckProg
import Definitions.Def_MIPRE_Foundations_Introspection_PauliStageProg
import Definitions.Def_MIPRE_Foundations_Introspection_FieldQuestionProg
import Definitions.Def_MIPRE_Background_AnswerReduction_DecideSpec
import Theorems.Thm_MIPRE_AnswerReduction_atom_ld1
import Theorems.Thm_MIPRE_AnswerReduction_atom_ld6

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.AnswerReduction
noncomputable section
open Finset MIPRE.CL SAT Pcp Cost StageProg Introspection.FieldLineCheck Introspection.FieldQuestionProgram Introspection.SeedProgram LIDT LIDT.CL
variable {k : ℕ} (hk : 1 ≤ k) {P : PcpParams}
/-- A point answer of the first five copies is one block. -/
theorem ansB_val1 {i : Fin 6} (hi : (i : ℕ) < 5) {u : Ans P ((shoupBinField k hk)).carrier}
    (hu : ansFmt (i, .point) u = true) :
    ∃ av : Fin 1 → ((shoupBinField k hk)).carrier, u = .inl (.values av) ∧ ansB hk u = ((shoupBinField k hk)).vecBits av ∧
      val1 u = av 0 := by
  rcases u with (av | f | f) | (av | f | f) <;>
    simp [ansFmt, tyFmt, hi] at hu <;> try omega
  refine ⟨av, rfl, ?_, rfl⟩
  simp [ansB, elems, BinField.vecBits]
end
end MIPRE.AnswerReduction

namespace MIPRE.AnswerReduction
noncomputable section
open Finset MIPRE.CL SAT Pcp Cost StageProg Introspection.FieldLineCheck Introspection.FieldQuestionProgram Introspection.SeedProgram LIDT LIDT.CL
variable {k : ℕ} (hk : 1 ≤ k) {P : PcpParams}
/-- A point answer of the sixth copy is its `m' + 6` blocks. -/
theorem ansB_val6 {i : Fin 6} (hi : (i : ℕ) = 5) {u : Ans P ((shoupBinField k hk)).carrier}
    (hu : ansFmt (i, .point) u = true) :
    ∃ av : Fin (P.m' + 6) → ((shoupBinField k hk)).carrier, u = .inr (.values av) ∧ ansB hk u = ((shoupBinField k hk)).vecBits av ∧
      vals6 u = av ∧ ∀ j, val6 j u = av j := by
  rcases u with (av | f | f) | (av | f | f) <;>
    simp [ansFmt, tyFmt, hi] at hu
  refine ⟨av, rfl, ?_, rfl, fun _ => rfl⟩
  simp [ansB, elems, BinField.vecBits]
end
end MIPRE.AnswerReduction

namespace MIPRE.AnswerReduction
noncomputable section
open Finset MIPRE.CL SAT Pcp Cost StageProg Introspection.FieldLineCheck Introspection.FieldQuestionProgram Introspection.SeedProgram LIDT LIDT.CL
variable {k : ℕ} (hk : 1 ≤ k) {P : PcpParams}
theorem getD_vecBits {N : ℕ} (v : Fin N → ((shoupBinField k hk)).carrier) (j : Fin N) :
    (((shoupBinField k hk)).vecBits v).getD j [] = ((shoupBinField k hk)).toBits (v j) := by
  simp [BinField.vecBits, List.getD_eq_getElem?_getD]
end
end MIPRE.AnswerReduction

namespace MIPRE.AnswerReduction
noncomputable section
open Finset MIPRE.CL SAT Pcp Cost StageProg Introspection.FieldLineCheck Introspection.FieldQuestionProgram Introspection.SeedProgram LIDT LIDT.CL
variable {k : ℕ} (hk : 1 ≤ k) {P : PcpParams}
theorem getD_vecBits' {N : ℕ} (v : Fin N → ((shoupBinField k hk)).carrier) (j : ℕ) (hj : j < N) :
    (((shoupBinField k hk)).vecBits v).getD j [] = ((shoupBinField k hk)).toBits (v ⟨j, hj⟩) :=
  getD_vecBits hk v ⟨j, hj⟩
end
end MIPRE.AnswerReduction

namespace MIPRE.AnswerReduction
noncomputable section
open Finset MIPRE.CL SAT Pcp Cost StageProg Introspection.FieldLineCheck Introspection.FieldQuestionProgram Introspection.SeedProgram LIDT LIDT.CL
variable {k : ℕ} (hk : 1 ≤ k) {P : PcpParams}
theorem toBits_injective : Function.Injective ((shoupBinField k hk)).toBits := fun a b h => by
  simpa only [((shoupBinField k hk)).ofBits_toBits] using congrArg ((shoupBinField k hk)).ofBits h
end
end MIPRE.AnswerReduction

namespace MIPRE.AnswerReduction
noncomputable section
open Finset MIPRE.CL SAT Pcp Cost StageProg Introspection.FieldLineCheck Introspection.FieldQuestionProgram Introspection.SeedProgram LIDT LIDT.CL
variable (F : PcpFamily) (n : ℕ)
theorem atom_val6_val1 {i i' : Fin 6} (hi : (i : ℕ) = 5) (hi' : (i' : ℕ) < 5)
    {u v : Ans (F.par n) (fld (F.par n) (F.hk n)).carrier} (hu : ansFmt (i, .point) u = true)
    (hv : ansFmt (i', .point) v = true) (j : Fin ((F.par n).m' + 6)) :
    decide (val6 j u = val1 v) = decide ((ansB (F.hk n) u).getD j [] = (ansB (F.hk n) v).getD 0 []) := by
  obtain ⟨av, -, hua, -, hv6⟩ := ansB_val6 (F.hk n) hi hu
  obtain ⟨bv, -, hvb, hv1⟩ := ansB_val1 (F.hk n) hi' hv
  rw [hua, hvb, hv6, hv1, getD_vecBits (F.hk n) av j, getD_vecBits' (F.hk n) bv 0 one_pos]
  simp only [(toBits_injective (F.hk n)).eq_iff]
  rfl
end
end MIPRE.AnswerReduction

namespace MIPRE.AnswerReduction
noncomputable section
open Finset MIPRE.CL SAT Pcp Cost StageProg Introspection.FieldLineCheck Introspection.FieldQuestionProgram Introspection.SeedProgram LIDT LIDT.CL
variable (F : PcpFamily) (n : ℕ)
theorem atom_val1_val6 {i i' : Fin 6} (hi : (i : ℕ) < 5) (hi' : (i' : ℕ) = 5)
    {u v : Ans (F.par n) (fld (F.par n) (F.hk n)).carrier} (hu : ansFmt (i, .point) u = true)
    (hv : ansFmt (i', .point) v = true) (j : Fin ((F.par n).m' + 6)) :
    decide (val1 u = val6 j v) = decide ((ansB (F.hk n) u).getD 0 [] = (ansB (F.hk n) v).getD j []) := by
  obtain ⟨av, -, hua, hu1⟩ := ansB_val1 (F.hk n) hi hu
  obtain ⟨bv, -, hvb, -, hv6⟩ := ansB_val6 (F.hk n) hi' hv
  rw [hua, hvb, hv6, hu1, getD_vecBits' (F.hk n) av 0 one_pos, getD_vecBits (F.hk n) bv j]
  simp only [(toBits_injective (F.hk n)).eq_iff]
  rfl
end
end MIPRE.AnswerReduction

namespace MIPRE.AnswerReduction
noncomputable section
open Finset MIPRE.CL SAT Pcp Cost StageProg Introspection.FieldLineCheck Introspection.FieldQuestionProgram Introspection.SeedProgram LIDT LIDT.CL
theorem chk_eq {C : Prop} [Decidable C] {chk c : Bool} (h : C → chk = c) :
    (!decide C || chk) = (if C then c else true) := by
  by_cases hC : C <;> simp [hC, h]
end
end MIPRE.AnswerReduction

namespace MIPRE.AnswerReduction
noncomputable section
open Finset MIPRE.CL SAT Pcp Cost StageProg Introspection.FieldLineCheck Introspection.FieldQuestionProgram Introspection.SeedProgram LIDT LIDT.CL
variable (F : PcpFamily) (n : ℕ) {X : Type*}
  (check : X → (Fin (F.par n).m' → Fq (F.par n) (F.hk n)) →
    (Fin ((F.par n).m' + 6) → Fq (F.par n) (F.hk n)) → Bool)
theorem getD_desc (c : Fin 6) : (List.ofFn (F.desc n)).getD c default = F.desc n c := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  simp
end
end MIPRE.AnswerReduction

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.AnswerReduction
open Finset MIPRE.CL SAT Pcp Cost StageProg Introspection.FieldLineCheck Introspection.FieldQuestionProgram Introspection.SeedProgram LIDT LIDT.CL
variable (F : PcpFamily) (n : ℕ) {X : Type*}
  (check : X → (Fin (F.par n).m' → Fq (F.par n) (F.hk n)) →
    (Fin ((F.par n).m' + 6) → Fq (F.par n) (F.hk n)) → Bool)
theorem _root_.solution (p q : Q (F.par n) (Fq (F.par n) (F.hk n)) X)
    (u v : Ans (F.par n) (Fq (F.par n) (F.hk n)))
    (hu : ansFmt p.1.2 u = true) (hv : ansFmt q.1.2 v = true) (chk : Bool)
    (hchk : chkPlan p.1 = true → chk = check p.2.1 ((regs6 (F.par n)).ptOf p.2.2) (vals6 u)) :
    sideB (unary (F.par n).k) (unary (F.par n).m') (List.ofFn (F.desc n)) chk p.1 q.1
        (blocksV (F.hk n) (F.par n) p.2.2) (blocksV (F.hk n) (F.par n) q.2.2)
        (ansB (F.hk n) u) (ansB (F.hk n) v) =
      side (F.sel n) (F.sel' n) check p q u v := by
  obtain ⟨⟨r, i, τ⟩, x, xv⟩ := p
  obtain ⟨⟨r', i', τ'⟩, y, yv⟩ := q
  simp only at hu hv hchk ⊢
  have hchk' := fun h => hchk (by simpa [chkPlan] using h)
  cases r <;> cases r' <;> simp only [sideB, side, eqPlan, ldPlan, chkPlan, roleIdx] at hchk' ⊢ <;>
    simp only [reduceCtorEq, and_false, false_and, if_false, true_and, and_true, if_true,
      Bool.true_and, Bool.and_true, Fin.val_zero, Fin.val_one, Fin.isValue,
      decide_false, Bool.not_false, Bool.true_or, zero_ne_one, one_ne_zero, and_self,
      IsEmpty.forall_iff] at hchk' ⊢
  · -- two oracles
    rw [chk_eq hchk']
    have hassoc : ∀ a b c d : Bool, (a && b && c && d) = (a && (b && c) && d) := by decide
    conv_rhs => rw [hassoc]
    congr 2
    · split_ifs with hC
      · obtain ⟨-, hi5, rfl, hi', rfl⟩ := hC
        exact (atom_val1_val6 F n hi5 hi' hu hv ⟨i, by omega⟩).symm
      · rfl
    · split_ifs with hB hC hC
      · exact absurd hC.1 (by omega)
      · obtain ⟨-, hi5, hii, rfl, hτ'⟩ := hB
        rw [hii] at hv
        have hi : i = (⟨i, hi5⟩ : Fin 5).castSucc := Fin.ext rfl
        rw [hi] at hu hv
        have := atom_ld1 F n ⟨i, hi5⟩ hτ' hu hv xv yv
        simp only [Bool.and_true, if_false, Bool.false_eq_true]
        rw [this, ← hi, getD_desc]
      · obtain ⟨hi5, hi5', rfl, hτ'⟩ := hC
        have hii : i' = i := Fin.ext (by omega)
        subst hii
        have := atom_ld6 F n hi5 hτ' hu hv xv yv
        simp only [Bool.true_and, if_true]
        rw [this, length_unary]
        exact congrArg (fun d => ldB _ d _ _ _ _ _) (getD_desc F n 5)
      · rfl
  · -- the oracle against Alice
    rw [chk_eq hchk']
    congr 1
    split_ifs with hC
    · obtain ⟨hi5, rfl, hi', rfl⟩ := hC
      exact (atom_val6_val1 F n hi5 (by omega) hu hv ⟨0, by omega⟩).symm
    · rfl
  · -- the oracle against Bob
    rw [chk_eq hchk']
    congr 1
    split_ifs with hC
    · obtain ⟨hi5, rfl, hi', rfl⟩ := hC
      exact (atom_val6_val1 F n hi5 (by omega) hu hv ⟨1, by omega⟩).symm
    · rfl
  · -- Alice against Alice
    split_ifs with hC
    · obtain ⟨hi, hi', rfl, hτ'⟩ := hC
      have e : i = (0 : Fin 5).castSucc := Fin.ext hi
      have e' : i' = (0 : Fin 5).castSucc := Fin.ext hi'
      subst e e'
      rw [atom_ld1 F n 0 hτ' hu hv xv yv]
      simp [List.getD_eq_getElem?_getD]
    · rfl
  · -- Bob against Bob
    split_ifs with hC
    · obtain ⟨hi, hi', rfl, hτ'⟩ := hC
      have e : i = (1 : Fin 5).castSucc := Fin.ext hi
      have e' : i' = (1 : Fin 5).castSucc := Fin.ext hi'
      subst e e'
      rw [atom_ld1 F n 1 hτ' hu hv xv yv]
      simp [List.getD_eq_getElem?_getD]
    · rfl
end MIPRE.AnswerReduction
