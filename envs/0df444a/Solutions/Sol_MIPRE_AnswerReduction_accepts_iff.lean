-- Prove2me | solution 1 for MIPRE.AnswerReduction.accepts_iff
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T07:03:41.001148+00:00
-- url     : https://prove2.me/submissions/cae9bf24-f9e4-44f2-b1b5-ff7d498a3d16

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/AnswerReduction/ArDecider.lean (solution of MIPRE.AnswerReduction.accepts_iff);
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
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Degree
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
import Mathlib.Tactic
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
import Definitions.Def_MIPRE_Foundations_Cost_SizeProgram
import Definitions.Def_MIPRE_Foundations_SAT_PcpFormat
import Definitions.Def_MIPRE_Foundations_Halting_Lists_B
import Definitions.Def_MIPRE_Foundations_Cost_Growth
import Definitions.Def_MIPRE_Foundations_Halting_Arith
import Definitions.Def_MIPRE_Foundations_Repeat_Prims
import Definitions.Def_MIPRE_Foundations_Repeat_MapLoop
import Definitions.Def_MIPRE_Foundations_Repeat_Sampler
import Definitions.Def_MIPRE_Foundations_CL_Repeat
import Definitions.Def_MIPRE_Foundations_Repeat_Bits
import Definitions.Def_MIPRE_Foundations_VerifierValue
import Definitions.Def_MIPRE_Foundations_Pipeline_Budget
import Definitions.Def_MIPRE_Foundations_Pipeline_Repetition
import Definitions.Def_MIPRE_Foundations_Repeat_RepSampler
import Definitions.Def_MIPRE_Foundations_Repeat_Dom
import Definitions.Def_MIPRE_Foundations_Repeat_SamplerCost
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgQueries
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgSampler
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgCost
import Definitions.Def_MIPRE_Foundations_OracularSampler
import Definitions.Def_MIPRE_Foundations_CL_DetypingDeciderRoute
import Definitions.Def_MIPRE_Foundations_CL_DetypingDeciderProg
import Definitions.Def_MIPRE_Foundations_CL_DetypingDecider
import Definitions.Def_MIPRE_Foundations_CL_DetypingDeciderGame
import Definitions.Def_MIPRE_Foundations_Halting_Serial
import Definitions.Def_MIPRE_Foundations_Cost_Kleene_B
import Definitions.Def_MIPRE_Foundations_OracularDecider
import Definitions.Def_MIPRE_Background_AnswerReduction_DecideProg
import Definitions.Def_MIPRE_Foundations_Cost_While
import Definitions.Def_MIPRE_Foundations_Pipeline_UnaryArith
import Definitions.Def_MIPRE_Foundations_Pipeline_AnswerReduction
import Definitions.Def_MIPRE_Background_AnswerReduction_Params
import Definitions.Def_MIPRE_Background_AnswerReduction_ArSampler
import Definitions.Def_MIPRE_Background_AnswerReduction_ArDecider
import Theorems.Thm_MIPRE_AnswerReduction_Pcp_toBits_pcp
import Theorems.Thm_MIPRE_AnswerReduction_StageProg_blocksOf_flatBits
import Theorems.Thm_MIPRE_AnswerReduction_chkV_eq
import Theorems.Thm_MIPRE_AnswerReduction_core_runs
import Theorems.Thm_MIPRE_AnswerReduction_pd_heads
import Theorems.Thm_MIPRE_AnswerReduction_verdictB_eq
import Theorems.Thm_MIPRE_AnswerReduction_verdictP_apply
import Theorems.Thm_MIPRE_CL_Detyping_Program_readBits_encode
import Theorems.Thm_MIPRE_Cost_Eval_deterministic
import Theorems.Thm_MIPRE_Cost_encode_injective
import Theorems.Thm_MIPRE_Cost_hardcode_time
import Theorems.Thm_MIPRE_Cost_hardcode_time_rev

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.CL
noncomputable section
open Finset Cost
variable {a b : ℕ}
theorem toBits_eq_append (x : Fin (a + b) → 𝔽₂) :
    toBits x = toBits (leftPart x) ++ toBits (rightPart x) := by
  simp only [toBits, List.ofFn_add, leftPart, rightPart]
  rfl
end
end MIPRE.CL

namespace MIPRE.CL
noncomputable section
open Finset Cost
variable {a b : ℕ}
theorem take_toBits (x : Fin (a + b) → 𝔽₂) : (toBits x).take a = toBits (leftPart x) := by
  rw [toBits_eq_append, List.take_left' (length_toBits _)]
end
end MIPRE.CL

namespace MIPRE.CL
noncomputable section
open Finset Cost
variable {a b : ℕ}
theorem drop_toBits (x : Fin (a + b) → 𝔽₂) : (toBits x).drop a = toBits (rightPart x) := by
  rw [toBits_eq_append, List.drop_left' (length_toBits _)]
end
end MIPRE.CL

namespace MIPRE.CL.Detyping.Program
section
open Cost Cost.PolyTimeFun Polynomial
theorem rawTruthProg_encode_bool (b : Bool) : rawTruthProg (encode b) = b := by cases b <;> rfl
end
end MIPRE.CL.Detyping.Program

namespace MIPRE.OracleDecider
section
open Cost Cost.PolyTimeFun
open CL CL.Detyping.Program
variable {ℓ : ℕ} (S : Sampler ℓ)
/-- The two marginal calls, through the universal machine. -/
theorem univ_marginal (n j : ℕ) (hj₁ : 1 ≤ j) (hj : j ≤ ℓ) (w : Player) (z : BitStr)
    (hz : z.length = S.dim n) :
    ∃ t, selfUniversal.univ.Runs (.cons (encode S.prog)
      (encode (n, Sampler.Query.marginal w j z))) (encode (margBits S n j w z)) t := by
  obtain ⟨t, ht⟩ := S.runs_marginal n w j z hj₁ hj hz
  obtain ⟨t', -, h'⟩ := selfUniversal.time_le _ _ _ _ ht
  exact ⟨t', h'⟩
end
end MIPRE.OracleDecider

namespace MIPRE.AnswerReduction
noncomputable section
open Cost Cost.PolyTimeFun CL CL.Detyping.Program Pipeline SAT Pcp StageProg ParRoutine
theorem leftBP_apply (l : BitStr) (d : Unary) : leftBP (l, d) = l.take (l.length - d.length) := by
  simp only [leftBP, comp_apply, pair_apply, fst_apply, snd_apply, reverse_apply, drop_apply]
  rw [List.drop_reverse]; simp
end
end MIPRE.AnswerReduction

namespace MIPRE.AnswerReduction
noncomputable section
open Cost Cost.PolyTimeFun CL CL.Detyping.Program Pipeline SAT Pcp StageProg ParRoutine
theorem rightBP_apply (l : BitStr) (d : Unary) : rightBP (l, d) = l.drop (l.length - d.length) := by
  simp only [rightBP, comp_apply, pair_apply, fst_apply, snd_apply, reverse_apply, take_apply]
  rw [List.take_reverse]; simp
end
end MIPRE.AnswerReduction

namespace MIPRE.AnswerReduction
noncomputable section
open Cost Cost.PolyTimeFun CL CL.Detyping.Program Pipeline SAT Pcp StageProg ParRoutine
variable (PD : PcpDecider) (ℓ : ℕ) (sp dp : Prog) (lam mu sigma n : ℕ) (u v : ArTy)
  (x y a b : BitStr)
theorem dimProg_pd' : dimProg ((family PD lam mu sigma).pd n) = dB PD lam mu sigma n := by
  have h := (family PD lam mu sigma).dimProg_pd n
  rw [← unary_length (dimProg _), h]
  rfl
end
end MIPRE.AnswerReduction

namespace MIPRE.AnswerReduction
noncomputable section
open Cost Cost.PolyTimeFun CL CL.Detyping.Program Pipeline SAT Pcp StageProg ParRoutine
variable (PD : PcpDecider) (ℓ : ℕ) (sp dp : Prog) (lam mu sigma n : ℕ) (u v : ArTy)
  (x y a b : BitStr)
variable (rxA rxB ryA ryB : Data)
theorem pdD_eq {j : ℕ} (d : Data) (h : pdD j d = (family PD lam mu sigma).pd n) :
    kD j d = unary (arPar PD lam mu sigma n).k ∧ m'D j d = unary (arPar PD lam mu sigma n).m' ∧
      dimProg (pdD j d) = dB PD lam mu sigma n := by
  obtain ⟨h1, h2, -⟩ := pd_heads PD lam mu sigma n
  simp only [kD, m'D, comp_apply, h, h1, h2, dimProg_pd', and_self]
end
end MIPRE.AnswerReduction

namespace MIPRE.AnswerReduction
noncomputable section
open Cost Cost.PolyTimeFun CL CL.Detyping.Program Pipeline SAT Pcp StageProg ParRoutine
variable (PD : PcpDecider) (ℓ : ℕ) (sp dp : Prog) (lam mu sigma n : ℕ) (u v : ArTy)
  (x y a b : BitStr)
variable (rxA rxB ryA ryB : Data)
theorem pBlocks_eq (j i : ℕ) (d : Data) (z : BitStr)
    (hpd : pdD j d = (family PD lam mu sigma).pd n) (hz : inp j i d = encode z) :
    pBlocks j i d = pBl PD lam mu sigma n z := by
  obtain ⟨hk, hm', hdim⟩ := pdD_eq PD lam mu sigma n d hpd
  simp only [pBlocks, comp_apply, pair_apply, hk, hm', qBits, hz, readBits_encode, hdim,
    blocksOfP_apply, pBl]
end
end MIPRE.AnswerReduction

namespace MIPRE.AnswerReduction
noncomputable section
open Cost Cost.PolyTimeFun CL CL.Detyping.Program Pipeline SAT Pcp StageProg ParRoutine
variable (PD : PcpDecider) (ℓ : ℕ) (sp dp : Prog) (lam mu sigma n : ℕ) (u v : ArTy)
  (x y a b : BitStr)
variable (rxA rxB ryA ryB : Data)
theorem readV_ctx8 : readV (ctx8 PD sp dp lam mu sigma n u v x y a b rxA rxB ryA ryB) =
    ((unary (arPar PD lam mu sigma n).k, unary (arPar PD lam mu sigma n).m',
      List.ofFn ((family PD lam mu sigma).desc n)),
      (chkV PD dp lam mu sigma n rxA rxB x u a, chkV PD dp lam mu sigma n ryA ryB y v b), (u, v),
      (pBl PD lam mu sigma n x, pBl PD lam mu sigma n y), (a, b)) := by
  have hpd : pdD 8 (ctx8 PD sp dp lam mu sigma n u v x y a b rxA rxB ryA ryB) =
      (family PD lam mu sigma).pd n := by
    simp [pdD, res, ctx8, ctx7, ctx6, ctx2, ctx1]
  obtain ⟨hk, hm', -⟩ := pdD_eq PD lam mu sigma n _ hpd
  obtain ⟨-, -, hds⟩ := pd_heads PD lam mu sigma n
  have hx : inp 8 2 (ctx8 PD sp dp lam mu sigma n u v x y a b rxA rxB ryA ryB) = encode x := by
    simp [inp, ctx8, ctx7, ctx6, ctx2, ctx1, ctx0, encode_prod]
  have hy : inp 8 4 (ctx8 PD sp dp lam mu sigma n u v x y a b rxA rxB ryA ryB) = encode y := by
    simp [inp, ctx8, ctx7, ctx6, ctx2, ctx1, ctx0, encode_prod]
  simp only [readV, pair_apply, comp_apply, hk, hm', map_apply, hpd, hds,
    pBlocks_eq PD lam mu sigma n 8 2 _ x hpd hx, pBlocks_eq PD lam mu sigma n 8 4 _ y hpd hy]
  simp only [res, inp, inpLast, ctx8, ctx7, ctx6, ctx2, ctx1, ctx0, encode_prod, comp_apply,
    tails_cons, tails_zero, treeHead_cons, treeTail_cons, readFinite_encode, rawTruthProg_encode_bool,
    readBits_encode]
end
end MIPRE.AnswerReduction

namespace MIPRE.AnswerReduction
noncomputable section
open Cost Cost.PolyTimeFun CL CL.Detyping.Program Pipeline SAT Pcp StageProg ParRoutine
variable (PD : PcpDecider) {ℓ : ℕ} (V : Verifier (ℓ + 1)) (lam mu sigma : ℕ)
variable (n : ℕ)
theorem leftBP_toBits (z : Fin (dim V n (((family PD lam mu sigma)).par n)) → 𝔽₂) :
    leftBP (toBits z, dB PD lam mu sigma n) = toBits (oraclePart V n (((family PD lam mu sigma)).par n) z) := by
  rw [leftBP_apply, length_toBits, length_unary, oraclePart, ← take_toBits]
  congr 1
  simp [dim, family]
end
end MIPRE.AnswerReduction

namespace MIPRE.AnswerReduction
noncomputable section
open Cost Cost.PolyTimeFun CL CL.Detyping.Program Pipeline SAT Pcp StageProg ParRoutine
variable (PD : PcpDecider) {ℓ : ℕ} (V : Verifier (ℓ + 1)) (lam mu sigma : ℕ)
variable (n : ℕ)
theorem rightBP_toBits (z : Fin (dim V n (((family PD lam mu sigma)).par n)) → 𝔽₂) :
    rightBP (toBits z, dB PD lam mu sigma n) =
      flatBits (((family PD lam mu sigma)).par n) (((family PD lam mu sigma)).hk n) (pcpPart V n (((family PD lam mu sigma)).par n) (((family PD lam mu sigma)).hk n) z) := by
  rw [rightBP_apply, length_toBits, length_unary, pcpPart, ← toBits_pcp]
  simp only [LinearEquiv.apply_symm_apply]
  rw [show dim V n (((family PD lam mu sigma)).par n) - pcpDim (arPar PD lam mu sigma n) *
      (arPar PD lam mu sigma n).k = V.sampler.dim n by simp [dim, family], drop_toBits]
end
end MIPRE.AnswerReduction

namespace MIPRE.AnswerReduction
noncomputable section
open Cost Cost.PolyTimeFun CL CL.Detyping.Program Pipeline SAT Pcp StageProg ParRoutine
variable (PD : PcpDecider) {ℓ : ℕ} (V : Verifier (ℓ + 1)) (lam mu sigma : ℕ)
variable (n : ℕ)
theorem pBl_toBits (z : Fin (dim V n (((family PD lam mu sigma)).par n)) → 𝔽₂) :
    pBl PD lam mu sigma n (toBits z) =
      blocksV (((family PD lam mu sigma)).hk n) (((family PD lam mu sigma)).par n) (pcpPart V n (((family PD lam mu sigma)).par n) (((family PD lam mu sigma)).hk n) z) := by
  rw [pBl, show arPar PD lam mu sigma n = ((family PD lam mu sigma)).par n from rfl, rightBP_toBits,
    blocksOf_flatBits]
  rfl
end
end MIPRE.AnswerReduction

namespace MIPRE.AnswerReduction
noncomputable section
open Cost Cost.PolyTimeFun CL CL.Detyping.Program Pipeline SAT Pcp StageProg ParRoutine
variable (PD : PcpDecider) {ℓ : ℕ} (V : Verifier (ℓ + 1)) (lam mu sigma : ℕ)
variable (n : ℕ)
/-- The input sampler's full marginal at the oracle half, in bits. -/
theorem margBits_oracle (w : Player) (z : Fin (dim V n (((family PD lam mu sigma)).par n)) → 𝔽₂) :
    OracleDecider.margBits V.sampler n (ℓ + 1) w (toBits (oraclePart V n (((family PD lam mu sigma)).par n) z)) =
      toBits ((V.sampler.cl n w).eval (oraclePart V n (((family PD lam mu sigma)).par n) z)) := by
  simp [OracleDecider.margBits]
end
end MIPRE.AnswerReduction

namespace MIPRE.AnswerReduction
noncomputable section
open Cost Cost.PolyTimeFun CL CL.Detyping.Program Pipeline SAT Pcp StageProg ParRoutine
variable (PD : PcpDecider) {ℓ : ℕ} (V : Verifier (ℓ + 1)) (lam mu sigma : ℕ)
variable (n : ℕ)
/-- The input sampler's runs on the marginal queries at a question's oracle half. -/
theorem margQ_runs (w : Player) (z : Fin (dim V n (((family PD lam mu sigma)).par n)) → 𝔽₂) :
    ∃ t, selfUniversal.univ.Runs (margQ PD ℓ V.sampler.prog lam mu sigma n w (toBits z))
      (encode (toBits ((V.sampler.cl n w).eval (oraclePart V n (((family PD lam mu sigma)).par n) z)))) t := by
  rw [margQ, leftBP_toBits, ← margBits_oracle]
  exact OracleDecider.univ_marginal V.sampler n (ℓ + 1) (by omega) le_rfl w _ (length_toBits _)
end
end MIPRE.AnswerReduction

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.AnswerReduction
open Cost Cost.PolyTimeFun CL CL.Detyping.Program Pipeline SAT Pcp StageProg ParRoutine
variable (PD : PcpDecider) {ℓ : ℕ} (V : Verifier (ℓ + 1)) (lam mu sigma : ℕ)
variable (n : ℕ)
theorem _root_.solution (u v : ArTy) (x y : Fin (dim V n (((family PD lam mu sigma)).par n)) → 𝔽₂) {B : ℕ}
    (a b : Verifier.Answers B) :
    (typedDecider PD V lam mu sigma).Accepts n u (toBits x) v (toBits y) a.1 b.1 ↔
      typedPred V n (((family PD lam mu sigma)).par n) (((family PD lam mu sigma)).hk n) (((family PD lam mu sigma)).sel n) (((family PD lam mu sigma)).sel' n)
        (chk PD V lam mu sigma n) B (u, x) (v, y) a b = true := by
  set rxA := encode (toBits ((V.sampler.cl n .alice).eval (oraclePart V n (((family PD lam mu sigma)).par n) x)))
  set rxB := encode (toBits ((V.sampler.cl n .bob).eval (oraclePart V n (((family PD lam mu sigma)).par n) x)))
  set ryA := encode (toBits ((V.sampler.cl n .alice).eval (oraclePart V n (((family PD lam mu sigma)).par n) y)))
  set ryB := encode (toBits ((V.sampler.cl n .bob).eval (oraclePart V n (((family PD lam mu sigma)).par n) y)))
  obtain ⟨t, hrun⟩ := core_runs PD ℓ V.sampler.prog V.decider.prog lam mu sigma n u v (toBits x)
    (toBits y) a.1 b.1 rxA rxB ryA ryB (margQ_runs PD V lam mu sigma n .alice x)
    (margQ_runs PD V lam mu sigma n .bob x) (margQ_runs PD V lam mu sigma n .alice y)
    (margQ_runs PD V lam mu sigma n .bob y)
  have hverdict : verdictP (readV (ctx8 PD V.sampler.prog V.decider.prog lam mu sigma n u v
      (toBits x) (toBits y) a.1 b.1 rxA rxB ryA ryB)) =
      typedPred V n (((family PD lam mu sigma)).par n) (((family PD lam mu sigma)).hk n) (((family PD lam mu sigma)).sel n) (((family PD lam mu sigma)).sel' n)
        (chk PD V lam mu sigma n) B (u, x) (v, y) a b := by
    rw [readV_ctx8, verdictP_apply, pBl_toBits, pBl_toBits]
    refine (verdictB_eq ((family PD lam mu sigma)) n (chk PD V lam mu sigma n)
      (u, oraclePart V n (((family PD lam mu sigma)).par n) x, pcpPart V n (((family PD lam mu sigma)).par n) (((family PD lam mu sigma)).hk n) x)
      (v, oraclePart V n (((family PD lam mu sigma)).par n) y, pcpPart V n (((family PD lam mu sigma)).par n) (((family PD lam mu sigma)).hk n) y) a.1 b.1 _ _
      (fun u' hu' hp => chkV_eq PD V lam mu sigma n u x a.1 u' hu' hp)
      (fun v' hv' hq => chkV_eq PD V lam mu sigma n v y b.1 v' hv' hq)).trans ?_
    unfold typedPred
    rcases parse (fld (((family PD lam mu sigma)).par n) (((family PD lam mu sigma)).hk n)) u.2 a.1 with _ | u' <;>
      rcases parse (fld (((family PD lam mu sigma)).par n) (((family PD lam mu sigma)).hk n)) v.2 b.1 with _ | v' <;> rfl
  rw [← hverdict]
  constructor
  · rintro ⟨time, hr⟩
    obtain ⟨t', -, hr'⟩ := hardcode_time_rev (core_closed PD ℓ) hr
    have := (Eval.deterministic hr' hrun).1
    exact (encode_injective this).symm
  · intro h
    rw [h] at hrun
    exact ⟨_, hardcode_time (core_closed PD ℓ) hrun⟩
end MIPRE.AnswerReduction
