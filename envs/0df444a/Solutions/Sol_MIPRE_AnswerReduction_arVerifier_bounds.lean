-- Prove2me | solution 1 for MIPRE.AnswerReduction.arVerifier_bounds
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T07:23:43.406482+00:00
-- url     : https://prove2.me/submissions/46e82df9-d21e-46b8-bda3-ec78f62218b1

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/AnswerReduction/Construction.lean (solution of MIPRE.AnswerReduction.arVerifier_bounds);
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
import Definitions.Def_MIPRE_Foundations_Pipeline_PowDom
import Definitions.Def_MIPRE_Foundations_Pipeline_PowDomRun
import Definitions.Def_MIPRE_Background_AnswerReduction_ParamsCost
import Definitions.Def_MIPRE_Foundations_CL_ProductSamplerCost
import Definitions.Def_MIPRE_Foundations_CL_ProgBuild
import Definitions.Def_MIPRE_Background_AnswerReduction_Construction
import Theorems.Thm_MIPRE_AnswerReduction_cutVal_pdom
import Theorems.Thm_MIPRE_AnswerReduction_parProg_time
import Theorems.Thm_MIPRE_AnswerReduction_params_pdom
import Theorems.Thm_MIPRE_AnswerReduction_total
import Theorems.Thm_MIPRE_AnswerReduction_typedArg_pdom
import Theorems.Thm_MIPRE_AnswerReduction_typedDecider_time
import Theorems.Thm_MIPRE_AnswerReduction_typedSampler_time
import Theorems.Thm_MIPRE_CL_Detyping_DeciderProgram_prog_time
import Theorems.Thm_MIPRE_CL_Detyping_Program_readBits_encode
import Theorems.Thm_MIPRE_CL_Detyping_sampler_time
import Theorems.Thm_MIPRE_Cost_seqProg_runs
import Theorems.Thm_MIPRE_Pipeline_PDom_poly

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.AnswerReduction.Pcp
noncomputable section
open Finset MIPRE.LIDT MIPRE.LIDT.CL SAT MIPRE.CL Cost
variable (P : PcpParams)
variable {F : Type*}
theorem pcpDim_eq : pcpDim P = 10 * P.m + 2 * P.s + 16 := by
  simp only [pcpDim, PcpParams.m']; ring
end
end MIPRE.AnswerReduction.Pcp

namespace MIPRE.CL.Detyping.DeciderProgram
noncomputable section
open Cost Cost.PolyTimeFun Program
variable {T : Type*} [Fintype T] [DecidableEq T] [SizedEncoding T]
variable {ℓ : ℕ} (E : T → T → Prop) [DecidableRel E]
variable (S : TypedSampler ℓ T) (D : TypedDecider T) (C : CutoffProgram)
/-- The outer answer cut is enforced globally, including malformed graph views. -/
theorem verifier_rejectsLong (hℓ : 0 < ℓ) (hD : D.Total) (n : ℕ) :
    (verifier E S D C hℓ hD).RejectsLong n (C.outer n) := by
  intro x y a b hlong haccept
  have h := (accepts_iff E S D C hD n x y a b).mp haccept
  rcases hlong with hlong | hlong
  · exact (Nat.not_lt_of_ge h.2.2.1) hlong
  · exact (Nat.not_lt_of_ge h.2.2.2.1) hlong
end
end MIPRE.CL.Detyping.DeciderProgram

namespace MIPRE.AnswerReduction
noncomputable section
open CL SAT Pcp
variable {ℓ : ℕ} (S : Sampler (ℓ + 1)) (PD : PcpDecider) (lam mu sigma : ℕ)
theorem typedSampler_dim (n : ℕ) :
    (typedSampler S PD lam mu sigma).dim n =
      S.dim n + Pcp.pcpDim (arPar PD lam mu sigma n) * (arPar PD lam mu sigma n).k := rfl
end
end MIPRE.AnswerReduction

namespace MIPRE.Pipeline.PDom
section
open Cost
variable {W X K : ℕ}
theorem of_le {c m e v v' : ℕ} (h : PDom W X K c m e v) (hv : v' ≤ v) : PDom W X K c m e v' :=
  hv.trans h
end
end MIPRE.Pipeline.PDom

namespace MIPRE.Pipeline.PDom
section
open Cost
variable {W X K : ℕ}
/-- The coefficient and the degree. -/
theorem le_final {c m e v : ℕ} (h : PDom W X K c m e v) :
    v ≤ (c * (W + 1) ^ m) ^ (K + 1) * X ^ (e * (K + 1)) := by
  refine h.trans (le_of_eq ?_)
  rw [mul_pow, pow_mul]
end
end MIPRE.Pipeline.PDom

namespace MIPRE.Pipeline.PDom
section
open Cost
variable {W X K : ℕ}
theorem mono (hX : 1 ≤ X) {c c' m m' e e' v : ℕ} (h : PDom W X K c m e v) (hc : c ≤ c')
    (hm : m ≤ m') (he : e ≤ e') : PDom W X K c' m' e' v := by
  refine h.trans (Nat.pow_le_pow_left ?_ _)
  exact Nat.mul_le_mul (Nat.mul_le_mul hc (Nat.pow_le_pow_right (by omega) hm))
    (Nat.pow_le_pow_right hX he)
end
end MIPRE.Pipeline.PDom

namespace MIPRE.Pipeline.PDom
section
open Cost
variable {W X K : ℕ}
/-- A base of at least one is below its `(K + 1)`-st power. -/
theorem le_pow_succ {a : ℕ} : a ≤ a ^ (K + 1) :=
  Nat.le_self_pow (by omega) a
end
end MIPRE.Pipeline.PDom

namespace MIPRE.Pipeline.PDom
section
open Cost
variable {W X K : ℕ}
theorem const (c : ℕ) : PDom W X K (c + 1) 0 0 c := by
  simp only [PDom, pow_zero, Nat.mul_one]
  exact (Nat.le_succ c).trans (le_pow_succ)
end
end MIPRE.Pipeline.PDom

namespace MIPRE.Pipeline.PDom
section
open Cost
variable {W X K : ℕ}
theorem ofLeW {v : ℕ} (h : v ≤ W) : PDom W X K 1 1 0 v := by
  simp only [PDom, pow_one, pow_zero, Nat.mul_one, Nat.one_mul]
  exact (h.trans (Nat.le_succ W)).trans (le_pow_succ)
end
end MIPRE.Pipeline.PDom

namespace MIPRE.Pipeline.PDom
section
open Cost
variable {W X K : ℕ}
theorem add (hX : 1 ≤ X) {c₁ c₂ m₁ m₂ e₁ e₂ v₁ v₂ : ℕ} (h₁ : PDom W X K c₁ m₁ e₁ v₁)
    (h₂ : PDom W X K c₂ m₂ e₂ v₂) :
    PDom W X K (c₁ + c₂) (max m₁ m₂) (max e₁ e₂) (v₁ + v₂) := by
  have h₁' := h₁.mono hX (c' := c₁) (m' := max m₁ m₂) (e' := max e₁ e₂) le_rfl (le_max_left _ _)
    (le_max_left _ _)
  have h₂' := h₂.mono hX (c' := c₂) (m' := max m₁ m₂) (e' := max e₁ e₂) le_rfl (le_max_right _ _)
    (le_max_right _ _)
  unfold PDom at h₁' h₂' ⊢
  refine (Nat.add_le_add h₁' h₂').trans ?_
  rw [Nat.add_mul, Nat.add_mul]
  exact pow_add_pow_le (Nat.zero_le _) (Nat.zero_le _) (by omega)
end
end MIPRE.Pipeline.PDom

namespace MIPRE.Pipeline.PDom
section
open Cost
variable {W X K : ℕ}
theorem pow {c m e v : ℕ} (h : PDom W X K c m e v) (p : ℕ) :
    PDom W X K (c ^ p) (m * p) (e * p) (v ^ p) := by
  unfold PDom at h ⊢
  refine (Nat.pow_le_pow_left h p).trans (le_of_eq ?_)
  rw [← pow_mul, Nat.mul_comm (K + 1) p, pow_mul]
  simp only [mul_pow, ← pow_mul]
end
end MIPRE.Pipeline.PDom

namespace MIPRE.Pipeline.PRuns
section
open Cost Cost.PolyTimeFun CL.Detyping.Program LowDegree.DegreeArithmetic
variable {W X K : ℕ}
theorem size_le {c m e : ℕ} {p : Prog} {x r : Data} (h : PRuns W X K c m e p x r) :
    PDom W X K c m e r.size :=
  let ⟨_, ht, hr⟩ := h
  ht.of_le hr.size_le
end
end MIPRE.Pipeline.PRuns

namespace MIPRE.Pipeline.PRuns
section
open Cost Cost.PolyTimeFun CL.Detyping.Program LowDegree.DegreeArithmetic
variable {W X K : ℕ}
theorem seq (hX : 1 ≤ X) {c₁ m₁ e₁ c₂ m₂ e₂ : ℕ} {p q : Prog} (hq : q.WellScoped 1)
    {x y r : Data} (h₁ : PRuns W X K c₁ m₁ e₁ p x y) (h₂ : PRuns W X K c₂ m₂ e₂ q y r) :
    PRuns W X K (c₁ + c₂ + 2) (max (max m₁ m₂) 0) (max (max e₁ e₂) 0) (seqProg p q) x r :=
  let ⟨_, hs, hp⟩ := h₁
  let ⟨_, ht, hq'⟩ := h₂
  ⟨_, (hs.add hX ht).add hX (PDom.const 1), seqProg_runs hq hp hq'⟩
end
end MIPRE.Pipeline.PRuns

namespace MIPRE.Pipeline.PRuns
section
open Cost Cost.PolyTimeFun CL.Detyping.Program LowDegree.DegreeArithmetic
variable {W X K : ℕ}
/-- **A polynomial-time function's code**, on an input of dominated size. -/
theorem ptf {α β : Type*} [SizedEncoding α] [SizedEncoding β] (f : PolyTimeFun α β)
    (c m e : ℕ) : ∃ C M E, ∀ {W X K : ℕ} (a : α), 1 ≤ X → PDom W X K c m e (esize a) →
      PRuns W X K C M E f.code (encode a) (encode (f a)) :=
  ⟨_, _, _, fun a hX ha => by
    obtain ⟨t, ht, hr⟩ := f.computes a
    exact ⟨t, (ha.poly hX f.timeBound).of_le ht, hr⟩⟩
end
end MIPRE.Pipeline.PRuns

namespace MIPRE.AnswerReduction
noncomputable section
open Cost Cost.PolyTimeFun CL CL.Detyping.Program Pipeline SAT Pcp StageProg
variable (PD : PcpDecider) (lam mu sigma : ℕ)
variable (R : Polynomial ℕ)
/-- The cutoff program's time. -/
theorem arCut_time : ∃ c m e, ∀ {W X : ℕ}, ParamsBound PD R → ∀ (lam mu sigma n : ℕ), 1 ≤ X →
    arQ lam mu n ≤ W → lam ≤ W → sigma ≤ W → n ≤ W →
    PRuns W X mu c m e (arCut PD lam mu sigma).prog (encode n)
      (encode ((arCut PD lam mu sigma).inner n, (arCut PD lam mu sigma).outer n)) := by
  obtain ⟨cp, mp, ep, hp⟩ := parProg_time PD R
  obtain ⟨cc, mc, ec, hc⟩ := PRuns.ptf cutP cp mp ep
  exact ⟨_, _, _, fun {W X} hR lam mu sigma n hX hQ hl hs hn => by
    have P1 := hp (W := W) (X := X) hR lam mu sigma n hX hQ hl hs hn
    have P2 := hc (W := W) (X := X) (K := mu) ((family PD lam mu sigma).pd n) hX P1.size_le
    rw [encode_data, cutP_pd] at P2
    exact PRuns.seq hX cutP.closed P1 P2⟩
end
end MIPRE.AnswerReduction

namespace MIPRE.AnswerReduction
noncomputable section
open Cost Cost.PolyTimeFun CL CL.Detyping.Program Pipeline SAT Pcp StageProg
variable (PD : PcpDecider) (lam mu sigma : ℕ)
variable (R : Polynomial ℕ)
/-- The PCP's parameters, in the form the cut and the dimension use. -/
theorem parA_pdom : ∃ c m e, ∀ {W X : ℕ}, ParamsBound PD R → ∀ (lam mu sigma n : ℕ), 1 ≤ X →
    arQ lam mu n ≤ W → sigma ≤ W → n ≤ W →
    PDom W X mu c m e (20 * ((arPar PD lam mu sigma n).k + (arPar PD lam mu sigma n).m +
      (arPar PD lam mu sigma n).s) + 20) := by
  obtain ⟨c, m, e, h⟩ := params_pdom PD R
  exact ⟨c, m, e, fun hR lam mu sigma n hX hQ hs hn => h hR lam mu sigma n hX hQ hs hn⟩
end
end MIPRE.AnswerReduction

namespace MIPRE.AnswerReduction
noncomputable section
open Cost Cost.PolyTimeFun CL CL.Detyping.Program Pipeline SAT Pcp StageProg
variable (PD : PcpDecider) (lam mu sigma : ℕ)
variable (R : Polynomial ℕ)
/-- The PCP half's width is dominated. -/
theorem pcpWidth_pdom : ∃ c m e, ∀ {W X : ℕ}, ParamsBound PD R → ∀ (lam mu sigma n : ℕ), 1 ≤ X →
    arQ lam mu n ≤ W → sigma ≤ W → n ≤ W →
    PDom W X mu c m e (pcpDim (arPar PD lam mu sigma n) * (arPar PD lam mu sigma n).k) := by
  obtain ⟨c, m, e, h⟩ := parA_pdom PD R
  exact ⟨_, _, _, fun {W X} hR lam mu sigma n hX hQ hs hn => by
    have hA := h (W := W) (X := X) hR lam mu sigma n hX hQ hs hn
    set P := arPar PD lam mu sigma n
    refine (hA.pow 2).of_le ?_
    rw [pcpDim_eq]
    calc (10 * P.m + 2 * P.s + 16) * P.k
        ≤ (20 * (P.k + P.m + P.s) + 20) * (20 * (P.k + P.m + P.s) + 20) :=
          Nat.mul_le_mul (by omega) (by omega)
      _ = _ := by ring⟩
end
end MIPRE.AnswerReduction

namespace MIPRE.AnswerReduction
noncomputable section
open Cost Cost.PolyTimeFun CL CL.Detyping.Program Pipeline SAT Pcp StageProg
variable (PD : PcpDecider) (lam mu sigma : ℕ)
variable (R : Polynomial ℕ)
/-- The detyped sampler's dimension is dominated. -/
theorem dim_pdom : ∃ c m e, ∀ {W X : ℕ}, ParamsBound PD R → ∀ (lam mu sigma n d : ℕ), 1 ≤ X →
    arQ lam mu n ≤ W → sigma ≤ W → n ≤ W → d ≤ W →
    PDom W X mu c m e (CL.Detyping.graphDim ArTy + (d +
      pcpDim (arPar PD lam mu sigma n) * (arPar PD lam mu sigma n).k)) := by
  obtain ⟨cw, mw, ew, hw⟩ := pcpWidth_pdom PD R
  exact ⟨_, _, _, fun {W X} hR lam mu sigma n d hX hQ hs hn hd => by
    have pw := hw (W := W) (X := X) hR lam mu sigma n hX hQ hs hn
    exact ((PDom.const (CL.Detyping.graphDim ArTy)).add hX ((PDom.ofLeW hd).add hX pw))⟩
end
end MIPRE.AnswerReduction

namespace MIPRE.AnswerReduction
noncomputable section
open Cost Cost.PolyTimeFun CL CL.Detyping.Program Pipeline SAT Pcp StageProg
variable (PD : PcpDecider) (lam mu sigma : ℕ)
variable (R : Polynomial ℕ)
/-- A monomial bound below the output bound. -/
theorem pow_le_pow_of_le {W K c m C M : ℕ} (hc : c ≤ C) (hm : m ≤ M) :
    (c * (W + 1) ^ m) ^ (K + 1) ≤ (C * (W + 1) ^ M) ^ (K + 1) :=
  Nat.pow_le_pow_left (Nat.mul_le_mul hc (Nat.pow_le_pow_right (by omega) hm)) _
end
end MIPRE.AnswerReduction

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.AnswerReduction
open Cost Cost.PolyTimeFun CL CL.Detyping.Program Pipeline SAT Pcp StageProg
variable (PD : PcpDecider) (lam mu sigma : ℕ)
variable (R : Polynomial ℕ)
theorem _root_.solution (ℓ : ℕ) (hR : ParamsBound PD R) : ∃ (bound : Polynomial ℕ) (deg : ℕ),
    (∀ (V : Verifier (ℓ + 1)) (lam mu sigma n : ℕ), V.Within n (inBudget lam mu n) →
      V.size ≤ sigma → (arVerifier PD lam mu sigma V).Within n
        (Budget.uniform (outBound bound lam mu sigma n) (outDegree deg mu))) ∧
    ∀ lam mu sigma n, cutVal (arPar PD lam mu sigma n) ≤ outBound bound lam mu sigma n := by
  obtain ⟨cT, mT, eT, hT⟩ := typedSampler_time ℓ PD R
  obtain ⟨cs, ms, ds, hs⟩ := CL.Detyping.sampler_time graph cT mT eT
  obtain ⟨cC, mC, eC, hC⟩ := arCut_time PD R
  obtain ⟨cd, md, ed, hd⟩ := typedArg_pdom PD R
  obtain ⟨cD, mD, eD, hD⟩ := typedDecider_time ℓ PD R cd md ed
  obtain ⟨cP, mP, eP, hP⟩ := CL.Detyping.DeciderProgram.prog_time graph cT mT eT cC mC eC cD mD eD
  obtain ⟨cm, mm, em, hdim⟩ := dim_pdom PD R
  obtain ⟨cc, mc, ec, hcut⟩ := cutVal_pdom PD R
  have hcutB : ∀ lam mu sigma n, cutVal (arPar PD lam mu sigma n) ≤
      outBound (Polynomial.C (cs + cP + cm + cc) * (Polynomial.X + 1) ^ (ms + mP + mm + mc))
        lam mu sigma n := by
    intro lam mu sigma n
    set W := arg lam mu sigma n with hWdef
    have hQ : arQ lam mu n ≤ W := by simp only [hWdef, arg, arQ]; omega
    have hs' : sigma ≤ W := by simp only [hWdef, arg]; omega
    have hn : n ≤ W := by simp only [hWdef, arg]; omega
    have hbd : outBound (Polynomial.C (cs + cP + cm + cc) *
        (Polynomial.X + 1) ^ (ms + mP + mm + mc)) lam mu sigma n =
        ((cs + cP + cm + cc) * (W + 1) ^ (ms + mP + mm + mc)) ^ (mu + 1) := by
      simp [outBound, hWdef]
    rw [hbd]
    have h := (hcut (W := W) (X := 1) hR lam mu sigma n le_rfl hQ hs' hn).le_final
    simp only [one_pow, Nat.mul_one] at h
    exact h.trans (pow_le_pow_of_le (by omega) (by omega))
  refine ⟨Polynomial.C (cs + cP + cm + cc) * (Polynomial.X + 1) ^ (ms + mP + mm + mc), ds + eP,
    fun V lam mu sigma n hV hsz => ?_, hcutB⟩
  set W := arg lam mu sigma n with hWdef
  have hQ : arQ lam mu n ≤ W := by simp only [hWdef, arg, arQ]; omega
  have hl : lam ≤ W := by simp only [hWdef, arg]; omega
  have hs' : sigma ≤ W := by simp only [hWdef, arg]; omega
  have hn : n ≤ W := by simp only [hWdef, arg]; omega
  have hSz : esize V.sampler.prog ≤ W :=
    ((le_max_left _ _).trans hsz).trans hs'
  have hDz : esize V.decider.prog ≤ W :=
    ((le_max_right _ _).trans hsz).trans hs'
  have hS : V.sampler.TimeBoundAt n (arQ lam mu n) mu := hV.sampler_time
  have hVd : V.sampler.dim n ≤ W := hV.sampler_dim.trans hQ
  have hbd : outBound (Polynomial.C (cs + cP + cm + cc) * (Polynomial.X + 1) ^ (ms + mP + mm + mc))
      lam mu sigma n = ((cs + cP + cm + cc) * (W + 1) ^ (ms + mP + mm + mc)) ^ (mu + 1) := by
    simp [outBound, hWdef]
  have hTS := hT (W := W) V.sampler lam mu sigma n hR hQ hl hs' hn hSz hS
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- the sampler's time
    simp only [Budget.uniform_S, Budget.uniform_k, hbd, outDegree]
    exact (hs (W := W) (K := mu) (typedSampler V.sampler PD lam mu sigma) (by unfold level; omega)
      n hn hTS).mono (pow_le_pow_of_le (by omega) (by omega))
      (Nat.mul_le_mul_right _ (by omega))
  · -- the dimension
    simp only [Budget.uniform_d, hbd]
    have h := (hdim (W := W) (X := 1) hR lam mu sigma n (V.sampler.dim n) le_rfl hQ hs' hn
      hVd).le_final
    simp only [one_pow, Nat.mul_one] at h
    exact h.trans (pow_le_pow_of_le (by omega) (by omega))
  · -- the decider's time
    simp only [Budget.uniform_D, Budget.uniform_k, hbd, outDegree]
    have hsdim : (typedSampler V.sampler PD lam mu sigma).dim n ≤
        W + pcpDim (arPar PD lam mu sigma n) * (arPar PD lam mu sigma n).k := by
      rw [typedSampler_dim]; omega
    refine (hP (W := W) (K := mu) (typedSampler V.sampler PD lam mu sigma)
      (typedDecider PD V lam mu sigma) (arCut PD lam mu sigma) n hn hTS
      (fun hX => hC hR lam mu sigma n hX hQ hl hs' hn)
      (fun {X} hX u v x y a b hx hy ha hb => ?_)).mono
      (pow_le_pow_of_le (by omega) (by omega)) (Nat.mul_le_mul_right _ (by omega))
    have hxl : (readBits (treeHead (treeTail (encode (u, x, v, y, a, b) : Data)))).length ≤
        W + (dB PD lam mu sigma n).length := by
      simp only [encode_prod, treeTail_cons, treeHead_cons, readBits_encode, length_unary, dB]
      omega
    have hyl : (readBits (treeHead (treeTail (treeTail (treeTail
        (encode (u, x, v, y, a, b) : Data)))))).length ≤ W + (dB PD lam mu sigma n).length := by
      simp only [encode_prod, treeTail_cons, treeHead_cons, readBits_encode, length_unary, dB]
      omega
    obtain ⟨r, t, ht, hr⟩ := hD (W := W) (X := X) V lam mu sigma n hR hX hQ hl hs' hn hSz hDz hS
      (encode (u, x, v, y, a, b)) (hd hR lam mu sigma n _ hX hQ hs' hn hsdim u v x y a b hx hy ha hb)
      hxl hyl
    exact ⟨r, t, ht, hr⟩
  · -- the answer cut
    simp only [Budget.uniform_B, hbd]
    exact Verifier.RejectsLong.mono ((hcutB lam mu sigma n).trans hbd.le)
      (CL.Detyping.DeciderProgram.verifier_rejectsLong graph
      (typedSampler V.sampler PD lam mu sigma) (typedDecider PD V lam mu sigma)
      (arCut PD lam mu sigma) _ (total PD V lam mu sigma) n)
end MIPRE.AnswerReduction
