-- Prove2me | solution 1 for MIPRE.AnswerReduction.typedDecider_time
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T06:59:24.147986+00:00
-- url     : https://prove2.me/submissions/7b9d67fe-3b21-49e2-a80c-2969436ae2ad

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/AnswerReduction/DeciderCost.lean (solution of MIPRE.AnswerReduction.typedDecider_time);
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
import Theorems.Thm_MIPRE_AnswerReduction_ParRoutine_budCore_closed
import Theorems.Thm_MIPRE_AnswerReduction_ParRoutine_core_closed
import Theorems.Thm_MIPRE_AnswerReduction_budCore_time
import Theorems.Thm_MIPRE_AnswerReduction_margCall_pdom
import Theorems.Thm_MIPRE_AnswerReduction_parCore_time
import Theorems.Thm_MIPRE_AnswerReduction_pd_heads
import Theorems.Thm_MIPRE_Cost_hardcode_time
import Theorems.Thm_MIPRE_Cost_seqProg_closed
import Theorems.Thm_MIPRE_Cost_seqProg_runs
import Theorems.Thm_MIPRE_Pipeline_PDom_poly
import Theorems.Thm_MIPRE_Pipeline_PRuns_stage

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
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
variable (PD : PcpDecider) {ℓ : ℕ} (V : Verifier (ℓ + 1)) (lam mu sigma : ℕ)
variable (n : ℕ)
theorem argMarg_general (j i : ℕ) (w : Player) (d : Data) (hsp : spD j d = encode V.sampler.prog)
    (hn : inp j 0 d = encode n) :
    argMarg ℓ j i w d = .cons (encode V.sampler.prog) (.cons (encode n)
      (encode ((1 : ℕ), w, ℓ + 1, oBits j i d, ([] : BitStr)))) := by
  simp only [argMarg, ap₂_apply, treePair_apply, comp_apply, pair_apply, const_apply,
    encoded_apply, hsp, hn]
end
end MIPRE.AnswerReduction

namespace MIPRE.AnswerReduction
noncomputable section
open Cost Cost.PolyTimeFun CL CL.Detyping.Program Pipeline SAT Pcp StageProg ParRoutine
variable (PD : PcpDecider) {ℓ : ℕ} (V : Verifier (ℓ + 1)) (lam mu sigma : ℕ)
variable (n : ℕ)
theorem argVer_general (j i it ia rA rB : ℕ) (d : Data) (hdp : dpD j d = encode V.decider.prog) :
    argVer j i it ia rA rB d = encode (pcpInput V.decider.prog (readNat (inp j 0 d))
      (readNat (treeTail (res (j - 2) d))) (readNat (treeHead (res (j - 2) d)))
      (readNat (treeTail (treeTail (lmsD j d)))) (readBits (res rA d)) (readBits (res rB d))
      (pBlocks j i d).1 (aBlocks j it ia d)) := by
  rw [argVer]
  simp only [ap₂_apply, treePair_apply, comp_apply, encoded_apply, hdp, fst_apply, pcpInput,
    encode_prod]
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
/-- An affine function of `W`. -/
theorem ofAffine {a b v : ℕ} (h : v ≤ a * W + b) : PDom W X K (a + b + 1) 1 0 v := by
  simp only [PDom, pow_one, pow_zero, Nat.mul_one]
  refine h.trans ((?_ : a * W + b ≤ (a + b + 1) * (W + 1)).trans le_pow_succ)
  nlinarith
end
end MIPRE.Pipeline.PDom

namespace MIPRE.Pipeline.PDom
section
open Cost
variable {W X K : ℕ}
/-- `K + 1 ≤ 2^{K + 1}`: the input sampler's degree itself is dominated. -/
theorem ofLeK {v : ℕ} (h : v ≤ K + 1) : PDom W X K 2 0 0 v := by
  simp only [PDom, pow_zero, Nat.mul_one]
  exact h.trans (Nat.lt_two_pow_self).le
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
theorem mul {c₁ c₂ m₁ m₂ e₁ e₂ v₁ v₂ : ℕ} (h₁ : PDom W X K c₁ m₁ e₁ v₁)
    (h₂ : PDom W X K c₂ m₂ e₂ v₂) : PDom W X K (c₁ * c₂) (m₁ + m₂) (e₁ + e₂) (v₁ * v₂) := by
  unfold PDom at h₁ h₂ ⊢
  refine (Nat.mul_le_mul h₁ h₂).trans (le_of_eq ?_)
  rw [← mul_pow, pow_add, pow_add]
  ring_nf
end
end MIPRE.Pipeline.PDom

namespace MIPRE.Pipeline.PDom
section
open Cost
variable {W X K : ℕ}
/-- A linear function of `W` and `K + 1`. -/
theorem ofLin (hX : 1 ≤ X) {a b c v : ℕ} (h : v ≤ a * W + b * (K + 1) + c) :
    PDom W X K (a + 2 * b + c + 3) 1 0 v := by
  have h1 : PDom W X K (a + c + 1) 1 0 (a * W + c) := ofAffine le_rfl
  have h2 : PDom W X K ((b + 1) * 2) 0 0 (b * (K + 1)) := (const b).mul (ofLeK le_rfl)
  refine ((h1.add hX h2).mono hX (by nlinarith) (by simp) (by simp)).of_le ?_
  omega
end
end MIPRE.Pipeline.PDom

namespace MIPRE.Pipeline
section
open Cost Cost.PolyTimeFun CL.Detyping.Program LowDegree.DegreeArithmetic
theorem esize_nat_le_four (x : ℕ) : esize x ≤ 4 * x + 1 :=
  (esize_nat_le x).trans (by have := Nat.size_le.mpr (Nat.lt_two_pow_self (n := x)); omega)
end
end MIPRE.Pipeline

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

namespace MIPRE.Pipeline.PRuns
section
open Cost Cost.PolyTimeFun CL.Detyping.Program LowDegree.DegreeArithmetic
variable {W X K : ℕ}
/-- A polynomial-time function's value, of dominated size. -/
theorem ptf_size {α β : Type*} [SizedEncoding α] [SizedEncoding β] (f : PolyTimeFun α β)
    (c m e : ℕ) : ∃ C M E, ∀ {W X K : ℕ} (a : α), 1 ≤ X → PDom W X K c m e (esize a) →
      PDom W X K C M E (esize (f a)) :=
  ⟨_, _, _, fun a hX ha => (ha.poly hX f.timeBound).of_le (f.esize_apply_le a)⟩
end
end MIPRE.Pipeline.PRuns

namespace MIPRE.Pipeline.PRuns
section
open Cost Cost.PolyTimeFun CL.Detyping.Program LowDegree.DegreeArithmetic
variable {W X K : ℕ}
/-- **Hardcoding** a datum `d`. -/
theorem hardcode (hX : 1 ≤ X) {c m e c₁ m₁ e₁ c₂ m₂ e₂ : ℕ} {p : Prog} (hp : p.WellScoped 1)
    {d x r : Data} (h : PRuns W X K c m e p (.cons d x) r) (hd : PDom W X K c₁ m₁ e₁ d.size)
    (hx : PDom W X K c₂ m₂ e₂ x.size) :
    PRuns W X K (c + c₁ + c₂ + 4) (max (max (max m m₁) m₂) 0) (max (max (max e e₁) e₂) 0)
      (Cost.hardcode p d) x r :=
  let ⟨_, ht, hr⟩ := h
  ⟨_, ((ht.add hX hd).add hX hx).add hX (PDom.const 3), hardcode_time hp hr⟩
end
end MIPRE.Pipeline.PRuns

namespace MIPRE.Pipeline.PRuns
section
open Cost Cost.PolyTimeFun CL.Detyping.Program LowDegree.DegreeArithmetic
variable {W X K : ℕ}
/-- **The universal machine**, simulating a run of dominated cost. -/
theorem univ (c m e : ℕ) : ∃ C M E, ∀ {W X K : ℕ} (q : Prog) (v r : Data) (t : ℕ), 1 ≤ X →
    q.Runs v r t → PDom W X K c m e (esize q + v.size + t) →
    PRuns W X K C M E selfUniversal.univ (.cons (encode q) v) r :=
  ⟨_, _, _, fun q v r t hX hr ht => by
    obtain ⟨t', ht', hu⟩ := selfUniversal.time_le q v r t hr
    exact ⟨t', (ht.poly hX selfUniversal.bound).of_le ht', hu⟩⟩
end
end MIPRE.Pipeline.PRuns

namespace MIPRE.AnswerReduction
noncomputable section
open Cost Cost.PolyTimeFun CL.Detyping.Program Pipeline SAT StageProg
theorem pdLin {W X K v : ℕ} (hX : 1 ≤ X) (h : v ≤ 40 * W + 40 * (K + 1) + 40) :
    PDom W X K linC 1 0 v :=
  PDom.ofLin hX h
end
end MIPRE.AnswerReduction

namespace MIPRE.AnswerReduction
noncomputable section
open Cost Cost.PolyTimeFun CL CL.Detyping.Program Pipeline SAT Pcp StageProg ParRoutine
/-- A context grows by one result. -/
theorem next_pdom (c m e c' m' e' : ℕ) : ∃ C M E, ∀ {W X K : ℕ} (x r : Data), 1 ≤ X →
    PDom W X K c m e x.size → PDom W X K c' m' e' r.size → PDom W X K C M E (Data.cons r x).size :=
  ⟨_, _, _, fun x r hX hx hr => by
    simpa only [Data.size_cons, Nat.add_comm r.size] using (hx.add hX hr).add hX (PDom.const 1)⟩
end
end MIPRE.AnswerReduction

namespace MIPRE.AnswerReduction
noncomputable section
open Cost Cost.PolyTimeFun CL CL.Detyping.Program Pipeline SAT Pcp StageProg ParRoutine
/-- The hardcoded data `(S̄, D̄, λ, μ, σ)`, at `K = μ`. -/
theorem hdat_pdom : ∃ c m e, ∀ {W X K : ℕ} (sp dp : Prog) (lam sigma : ℕ), 1 ≤ X →
    esize sp ≤ W → esize dp ≤ W → lam ≤ W → sigma ≤ W →
    PDom W X K c m e (encode (sp, dp, lam, K, sigma) : Data).size := by
  exact ⟨_, _, _, fun {W X K} sp dp lam sigma hX hsp hdp hl hs => by
    have el := esize_nat_le_four lam
    have em := esize_nat_le_four K
    have es := esize_nat_le_four sigma
    refine (pdLin hX (by omega : esize sp + esize dp + (4 * lam + 1) + (4 * K + 1) +
      (4 * sigma + 1) + 4 ≤ 40 * W + 40 * (K + 1) + 40)).of_le ?_
    simp only [encode_prod, Data.size_cons]
    change esize sp + (esize dp + (esize lam + (esize K + esize sigma + 1) + 1) + 1) + 1 ≤ _
    omega⟩
end
end MIPRE.AnswerReduction

namespace MIPRE.AnswerReduction
noncomputable section
open Cost Cost.PolyTimeFun CL CL.Detyping.Program Pipeline SAT Pcp StageProg ParRoutine
/-- The index and the rest of the input. -/
theorem input_pdom (cd md ed : ℕ) : ∃ c m e, ∀ {W X K : ℕ} (n : ℕ) (d : Data), 1 ≤ X →
    n ≤ W → PDom W X K cd md ed d.size → PDom W X K c m e (Data.cons (encode n) d).size := by
  exact ⟨_, _, _, fun {W X K} n d hX hn hd => by
    have en := esize_nat_le_four n
    refine ((PDom.ofAffine (a := 4) (b := 2) (by omega : esize n + 1 ≤ 4 * W + 2)).add hX
      hd).of_le ?_
    simp only [Data.size_cons]
    change esize n + d.size + 1 ≤ _
    omega⟩
end
end MIPRE.AnswerReduction

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.AnswerReduction
open Cost Cost.PolyTimeFun CL CL.Detyping.Program Pipeline SAT Pcp StageProg ParRoutine
theorem _root_.solution (ℓ : ℕ) (PD : PcpDecider) (R : Polynomial ℕ) (cd md ed : ℕ) :
    ∃ C M E, ∀ {W X : ℕ} (V : Verifier (ℓ + 1)) (lam mu sigma n : ℕ), ParamsBound PD R →
    1 ≤ X → arQ lam mu n ≤ W → lam ≤ W → sigma ≤ W → n ≤ W → esize V.sampler.prog ≤ W →
    esize V.decider.prog ≤ W → V.sampler.TimeBoundAt n (arQ lam mu n) mu →
    ∀ d : Data, PDom W X mu cd md ed d.size →
    (readBits (treeHead (treeTail d))).length ≤ W + (dB PD lam mu sigma n).length →
    (readBits (treeHead (treeTail (treeTail (treeTail d))))).length ≤
      W + (dB PD lam mu sigma n).length →
    ∃ r t, PDom W X mu C M E t ∧
      (typedDecider PD V lam mu sigma).prog.Runs (.cons (encode n) d) r t := by
  obtain ⟨cH, mH, eH, hH⟩ := hdat_pdom
  obtain ⟨cI, mI, eI, hI⟩ := input_pdom cd md ed
  obtain ⟨c0, m0, e0, h0⟩ := next_pdom cI mI eI cH mH eH
  obtain ⟨cp, mp, ep, hp⟩ := parCore_time PD R
  obtain ⟨c1, m1, e1, h1⟩ := PRuns.stage (ap₂ treePair (argPar 0) (PolyTimeFun.id Data))
    postKeep c0 m0 e0 cp mp ep
  obtain ⟨x1c, x1m, x1e, hx1⟩ := next_pdom c0 m0 e0 cp mp ep
  obtain ⟨cb, mb, eb, hb⟩ := budCore_time
  obtain ⟨c2, m2, e2, h2⟩ := PRuns.stage (ap₂ treePair (argPar 1) (PolyTimeFun.id Data))
    postKeep x1c x1m x1e cb mb eb
  obtain ⟨x2c, x2m, x2e, hx2⟩ := next_pdom x1c x1m x1e cb mb eb
  obtain ⟨cm, mm, em, hm⟩ := margCall_pdom ℓ
  obtain ⟨cu, mu', eu, hu⟩ := PRuns.univ cm mm em
  obtain ⟨c3, m3, e3, h3⟩ := PRuns.stage (ap₂ treePair (argMarg ℓ 2 2 .alice) (PolyTimeFun.id Data))
    postKeep x2c x2m x2e cu mu' eu
  obtain ⟨x3c, x3m, x3e, hx3⟩ := next_pdom x2c x2m x2e cu mu' eu
  obtain ⟨c4, m4, e4, h4⟩ := PRuns.stage (ap₂ treePair (argMarg ℓ 3 2 .bob) (PolyTimeFun.id Data))
    postKeep x3c x3m x3e cu mu' eu
  obtain ⟨x4c, x4m, x4e, hx4⟩ := next_pdom x3c x3m x3e cu mu' eu
  obtain ⟨c5, m5, e5, h5⟩ := PRuns.stage (ap₂ treePair (argMarg ℓ 4 4 .alice) (PolyTimeFun.id Data))
    postKeep x4c x4m x4e cu mu' eu
  obtain ⟨x5c, x5m, x5e, hx5⟩ := next_pdom x4c x4m x4e cu mu' eu
  obtain ⟨c6, m6, e6, h6⟩ := PRuns.stage (ap₂ treePair (argMarg ℓ 5 4 .bob) (PolyTimeFun.id Data))
    postKeep x5c x5m x5e cu mu' eu
  obtain ⟨x6c, x6m, x6e, hx6⟩ := next_pdom x5c x5m x5e cu mu' eu
  obtain ⟨a7c, a7m, a7e, ha7⟩ := PRuns.ptf_size (argVer 6 2 1 5 3 2) x6c x6m x6e
  obtain ⟨v7c, v7m, v7e, hv7⟩ := PRuns.ptf PD.verify a7c a7m a7e
  obtain ⟨c7, m7, e7, h7⟩ := PRuns.stage (ap₂ treePair (argVer 6 2 1 5 3 2) (PolyTimeFun.id Data))
    postKeep x6c x6m x6e v7c v7m v7e
  obtain ⟨x7c, x7m, x7e, hx7⟩ := next_pdom x6c x6m x6e v7c v7m v7e
  obtain ⟨a8c, a8m, a8e, ha8⟩ := PRuns.ptf_size (argVer 7 4 3 6 2 1) x7c x7m x7e
  obtain ⟨v8c, v8m, v8e, hv8⟩ := PRuns.ptf PD.verify a8c a8m a8e
  obtain ⟨c8, m8, e8, h8⟩ := PRuns.stage (ap₂ treePair (argVer 7 4 3 6 2 1) (PolyTimeFun.id Data))
    postKeep x7c x7m x7e v8c v8m v8e
  obtain ⟨x8c, x8m, x8e, hx8⟩ := next_pdom x7c x7m x7e v8c v8m v8e
  obtain ⟨cf, mf, ef, hf⟩ := PRuns.ptf (verdictP.comp readV) x8c x8m x8e
  exact ⟨_, _, _, fun {W X} V lam mu sigma n hR hX hQ hl hs hn hsp hdp hS d hd hxd hyd => by
    have hu' := selfUniversal.closed
    have hv' := PD.verify.closed
    set H : Data := encode (V.sampler.prog, V.decider.prog, lam, mu, sigma) with hHdef
    have pH : PDom W X mu cH mH eH H.size :=
      hH V.sampler.prog V.decider.prog lam sigma hX hsp hdp hl hs
    have pI : PDom W X mu cI mI eI (Data.cons (encode n) d).size :=
      hI n d hX hn hd
    set X0 : Data := .cons H (.cons (encode n) d) with hX0def
    have pX0 : PDom W X mu c0 m0 e0 X0.size := h0 _ _ hX pI pH
    -- stage 1
    have hpre1 : (ap₂ treePair (argPar 0) (PolyTimeFun.id Data)) X0 =
        .cons (.cons (encode (lam, mu, sigma)) (encode n)) X0 := by
      simp [argPar, lmsD, hdat, inp, X0, H, encode_prod]
    have P1 := hp (W := W) (X := X) hR lam mu sigma n hX hQ hl hs hn
    have S1 := h1 (ParRoutine.core_closed PD) X0 _ X0 _ hX hpre1 pX0 P1
    simp only [postKeep, ap₂_apply, treePair_apply, fst_apply, snd_apply] at S1
    set X1 : Data := .cons ((family PD lam mu sigma).pd n) X0 with hX1def
    have pX1 : PDom W X mu x1c x1m x1e X1.size := hx1 _ _ hX pX0 P1.size_le
    -- stage 2
    have hpre2 : (ap₂ treePair (argPar 1) (PolyTimeFun.id Data)) X1 =
        .cons (.cons (encode (lam, mu, sigma)) (encode n)) X1 := by
      simp [argPar, lmsD, hdat, inp, X1, X0, H, encode_prod]
    have P2 := hb (W := W) (X := X) lam mu sigma n hX hQ hl hs hn
    have S2 := h2 budCore_closed X1 _ X1 _ hX hpre2 pX1 P2
    simp only [postKeep, ap₂_apply, treePair_apply, fst_apply, snd_apply] at S2
    set X2 : Data := .cons (encode (arQ lam mu n, tPcp lam mu n)) X1 with hX2def
    have pX2 : PDom W X mu x2c x2m x2e X2.size := hx2 _ _ hX pX1 P2.size_le
    -- stages 3 to 6: the marginals
    have marg : ∀ (j i : ℕ) (w : Player) (Xj : Data),
        spD j Xj = encode V.sampler.prog → inp j 0 Xj = encode n →
        pdD j Xj = (family PD lam mu sigma).pd n →
        (readBits (inp j i Xj)).length ≤ W + (dB PD lam mu sigma n).length →
        ∃ r, PRuns W X mu cu mu' eu selfUniversal.univ (argMarg ℓ j i w Xj) r := by
      intro j i w Xj hspj hnj hpdj hlen
      rw [argMarg_general V n j i w Xj hspj hnj]
      set q : Data := encode ((1 : ℕ), w, ℓ + 1, oBits j i Xj, ([] : BitStr))
      have hob : (oBits j i Xj).length ≤ W := by
        obtain ⟨-, -, hdim⟩ := pdD_eq PD lam mu sigma n Xj hpdj
        simp only [oBits, comp_apply, pair_apply, hdim, leftBP_apply, qBits, List.length_take]
        omega
      have hq : q.size + 1 ≤ (4 * ℓ + 44) * (W + 1) := by
        have : q.size ≤ 4 * W + 4 * ℓ + 40 := by
          have h := esize_bitStr_le (oBits j i Xj)
          have h2 := esize_nat_le_four (ℓ + 1)
          have h3 : esize w ≤ 3 := by cases w <;> decide
          have h4 : esize (1 : ℕ) ≤ 5 := by decide
          have h5 : esize ([] : BitStr) = 1 := rfl
          simp only [q, encode_prod, Data.size_cons]
          change esize (1 : ℕ) + (esize w + (esize (ℓ + 1) + (esize (oBits j i Xj) +
            esize ([] : BitStr) + 1) + 1) + 1) + 1 ≤ _
          omega
        nlinarith
      obtain ⟨r, t, ht, hr⟩ := hS q
      exact ⟨r, hu V.sampler.prog (.cons (encode n) q) r t hX hr
        (hm V.sampler.prog n (arQ lam mu n) q t hX hsp hn hQ hq ht)⟩
    obtain ⟨rxA, P3⟩ := marg 2 2 .alice X2
      (by simp [spD, hdat, X2, X1, X0, H, encode_prod]) (by simp [inp, X2, X1, X0])
      (by simp [pdD, res, X2, X1]) (by simpa [inp, X2, X1, X0, tails, comp_apply] using hxd)
    have S3 := h3 hu' X2 _ X2 _ hX (by simp) pX2 P3
    simp only [postKeep, ap₂_apply, treePair_apply, fst_apply, snd_apply] at S3
    set X3 : Data := .cons rxA X2 with hX3def
    have pX3 : PDom W X mu x3c x3m x3e X3.size := hx3 _ _ hX pX2 P3.size_le
    obtain ⟨rxB, P4⟩ := marg 3 2 .bob X3
      (by simp [spD, hdat, X3, X2, X1, X0, H, encode_prod]) (by simp [inp, X3, X2, X1, X0])
      (by simp [pdD, res, X3, X2, X1]) (by simpa [inp, X3, X2, X1, X0, tails, comp_apply] using hxd)
    have S4 := h4 hu' X3 _ X3 _ hX (by simp) pX3 P4
    simp only [postKeep, ap₂_apply, treePair_apply, fst_apply, snd_apply] at S4
    set X4 : Data := .cons rxB X3 with hX4def
    have pX4 : PDom W X mu x4c x4m x4e X4.size := hx4 _ _ hX pX3 P4.size_le
    obtain ⟨ryA, P5⟩ := marg 4 4 .alice X4
      (by simp [spD, hdat, X4, X3, X2, X1, X0, H, encode_prod])
      (by simp [inp, X4, X3, X2, X1, X0]) (by simp [pdD, res, X4, X3, X2, X1])
      (by simpa [inp, X4, X3, X2, X1, X0, tails, comp_apply] using hyd)
    have S5 := h5 hu' X4 _ X4 _ hX (by simp) pX4 P5
    simp only [postKeep, ap₂_apply, treePair_apply, fst_apply, snd_apply] at S5
    set X5 : Data := .cons ryA X4 with hX5def
    have pX5 : PDom W X mu x5c x5m x5e X5.size := hx5 _ _ hX pX4 P5.size_le
    obtain ⟨ryB, P6⟩ := marg 5 4 .bob X5
      (by simp [spD, hdat, X5, X4, X3, X2, X1, X0, H, encode_prod])
      (by simp [inp, X5, X4, X3, X2, X1, X0]) (by simp [pdD, res, X5, X4, X3, X2, X1])
      (by simpa [inp, X5, X4, X3, X2, X1, X0, tails, comp_apply] using hyd)
    have S6 := h6 hu' X5 _ X5 _ hX (by simp) pX5 P6
    simp only [postKeep, ap₂_apply, treePair_apply, fst_apply, snd_apply] at S6
    set X6 : Data := .cons ryB X5 with hX6def
    have pX6 : PDom W X mu x6c x6m x6e X6.size := hx6 _ _ hX pX5 P6.size_le
    -- stages 7 and 8: the game checks
    obtain ⟨c7i, e7⟩ : ∃ c : PcpInput, argVer 6 2 1 5 3 2 X6 = encode c :=
      ⟨_, argVer_general V 6 2 1 5 3 2 X6
        (by simp [dpD, hdat, X6, X5, X4, X3, X2, X1, X0, H, encode_prod])⟩
    have pa7 : PDom W X mu a7c a7m a7e (esize c7i) := by
      have := ha7 (W := W) (K := mu) X6 hX pX6
      rw [e7] at this
      exact this
    have P7 := hv7 (W := W) (X := X) (K := mu) c7i hX pa7
    rw [← e7] at P7
    have S7 := h7 hv' X6 _ X6 _ hX (by simp) pX6 P7
    simp only [postKeep, ap₂_apply, treePair_apply, fst_apply, snd_apply] at S7
    set X7 : Data := .cons (encode (PD.verify c7i)) X6 with hX7def
    have pX7 : PDom W X mu x7c x7m x7e X7.size := hx7 _ _ hX pX6 P7.size_le
    obtain ⟨c8i, e8⟩ : ∃ c : PcpInput, argVer 7 4 3 6 2 1 X7 = encode c :=
      ⟨_, argVer_general V 7 4 3 6 2 1 X7
        (by simp [dpD, hdat, X7, X6, X5, X4, X3, X2, X1, X0, H, encode_prod])⟩
    have pa8 : PDom W X mu a8c a8m a8e (esize c8i) := by
      have := ha8 (W := W) (K := mu) X7 hX pX7
      rw [e8] at this
      exact this
    have P8 := hv8 (W := W) (X := X) (K := mu) c8i hX pa8
    rw [← e8] at P8
    have S8 := h8 hv' X7 _ X7 _ hX (by simp) pX7 P8
    simp only [postKeep, ap₂_apply, treePair_apply, fst_apply, snd_apply] at S8
    set X8 : Data := .cons (encode (PD.verify c8i)) X7 with hX8def
    have pX8 : PDom W X mu x8c x8m x8e X8.size := hx8 _ _ hX pX7 P8.size_le
    -- the verdict
    have P9 := hf (W := W) (X := X) (K := mu) X8 hX pX8
    rw [encode_data] at P9
    have hc := PolyTimeFun.closed (verdictP.comp readV)
    have Pcore := PRuns.seq hX (seqProg_closed (stg_closed _ budCore_closed) <|
        seqProg_closed (stg_closed _ hu') <| seqProg_closed (stg_closed _ hu') <|
        seqProg_closed (stg_closed _ hu') <| seqProg_closed (stg_closed _ hu') <|
        seqProg_closed (stg_closed _ hv') <| seqProg_closed (stg_closed _ hv') hc) S1 <|
      PRuns.seq hX (seqProg_closed (stg_closed _ hu') <| seqProg_closed (stg_closed _ hu') <|
        seqProg_closed (stg_closed _ hu') <| seqProg_closed (stg_closed _ hu') <|
        seqProg_closed (stg_closed _ hv') <| seqProg_closed (stg_closed _ hv') hc) S2 <|
      PRuns.seq hX (seqProg_closed (stg_closed _ hu') <| seqProg_closed (stg_closed _ hu') <|
        seqProg_closed (stg_closed _ hu') <| seqProg_closed (stg_closed _ hv') <|
        seqProg_closed (stg_closed _ hv') hc) S3 <|
      PRuns.seq hX (seqProg_closed (stg_closed _ hu') <| seqProg_closed (stg_closed _ hu') <|
        seqProg_closed (stg_closed _ hv') <| seqProg_closed (stg_closed _ hv') hc) S4 <|
      PRuns.seq hX (seqProg_closed (stg_closed _ hu') <| seqProg_closed (stg_closed _ hv') <|
        seqProg_closed (stg_closed _ hv') hc) S5 <|
      PRuns.seq hX (seqProg_closed (stg_closed _ hv') <| seqProg_closed (stg_closed _ hv') hc) S6 <|
      PRuns.seq hX (seqProg_closed (stg_closed _ hv') hc) S7 <|
      PRuns.seq hX hc S8 P9
    obtain ⟨t, ht, hr⟩ := PRuns.hardcode hX (core_closed PD ℓ) (show PRuns _ _ _ _ _ _ (core PD ℓ)
      (.cons H (.cons (encode n) d)) _ from Pcore) pH pI
    exact ⟨_, t, ht, hr⟩⟩
end MIPRE.AnswerReduction
