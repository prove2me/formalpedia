-- Prove2me | solution 1 for MIPRE.AnswerReduction.core_runs
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T06:59:23.476453+00:00
-- url     : https://prove2.me/submissions/d1a862a2-84a9-49d3-8263-cef928a2b609

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/AnswerReduction/ArDecider.lean (solution of MIPRE.AnswerReduction.core_runs);
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
import Theorems.Thm_MIPRE_AnswerReduction_ParRoutine_budCore_closed
import Theorems.Thm_MIPRE_AnswerReduction_ParRoutine_core_closed
import Theorems.Thm_MIPRE_AnswerReduction_budCore_runs
import Theorems.Thm_MIPRE_AnswerReduction_parCore_runs
import Theorems.Thm_MIPRE_AnswerReduction_pd_heads
import Theorems.Thm_MIPRE_CL_Detyping_Program_readBits_encode
import Theorems.Thm_MIPRE_CL_Detyping_Program_readNat_encode
import Theorems.Thm_MIPRE_Cost_seqProg_closed
import Theorems.Thm_MIPRE_Cost_seqProg_runs

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.Cost.Prog
section
open PolyTimeFun
theorem callWithContext_closed {p : Prog} (hp : p.WellScoped 1)
    (post : PolyTimeFun (Data × Data) Data) : (callWithContext p post).WellScoped 1 := by
  refine ⟨fstProg_wellScoped, hp.mono (by omega) _, ?_⟩
  exact ⟨⟨callVar_wellScoped (by decide) sndProg_wellScoped, by simp [WellScoped]⟩,
    post.closed.mono (by omega) _⟩
end
end MIPRE.Cost.Prog

namespace MIPRE.Cost.Prog
section
open PolyTimeFun
theorem callWithContext_runs {p : Prog} (hp : p.WellScoped 1)
    (post : PolyTimeFun (Data × Data) Data) (a ctx r : Data) (time : ℕ)
    (hr : p.Runs a r time) :
    ∃ t, (callWithContext p post).Runs (.cons a ctx) (post (ctx, r)) t := by
  obtain ⟨tp, _, hpRun⟩ := post.computes (ctx, r)
  have ectx := callVar_eval (env := [r, a, Data.cons a ctx]) (i := 2)
    sndProg_wellScoped (by simp) (sndProg_runs a ctx)
  exact ⟨_, Eval.let_ (fstProg_runs a ctx)
    (Eval.let_ (Eval.append_of_wellScoped hr hp _)
      (Eval.let_ (Eval.cons ectx (Eval.var_of_get (i := 0) (by simp)))
        (Eval.append_of_wellScoped hpRun post.closed _)))⟩
end
end MIPRE.Cost.Prog

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

namespace MIPRE.Pipeline
section
open Cost Cost.PolyTimeFun CL.Detyping.Program LowDegree.DegreeArithmetic
theorem stageProg_runs (pre : PolyTimeFun Data Data) {p : Prog} (hp : p.WellScoped 1)
    (post : PolyTimeFun (Data × Data) Data) (X a ctx r : Data) (t : ℕ)
    (hpre : pre X = .cons a ctx) (hr : p.Runs a r t) :
    ∃ t', (stageProg pre p post).Runs X (post (ctx, r)) t' := by
  obtain ⟨t₀, -, h₀⟩ := pre.computes X
  rw [encode_data, hpre] at h₀
  obtain ⟨t₁, h₁⟩ := Prog.callWithContext_runs hp post a ctx r t hr
  exact ⟨_, seqProg_runs (Prog.callWithContext_closed hp post) h₀ h₁⟩
end
end MIPRE.Pipeline

namespace MIPRE.AnswerReduction.ParRoutine
noncomputable section
open Cost Cost.PolyTimeFun CL.Detyping.Program Pipeline SAT StageProg
variable (PD : PcpDecider) (lam mu sigma : ℕ)
theorem seq_runs {p q : Prog} (hq : q.WellScoped 1) {x y r : Data}
    (hp : ∃ t, p.Runs x y t) (hq' : ∃ t, q.Runs y r t) : ∃ t, (seqProg p q).Runs x r t := by
  obtain ⟨s, hs⟩ := hp
  obtain ⟨t, ht⟩ := hq'
  exact ⟨_, seqProg_runs hq hs ht⟩
end
end MIPRE.AnswerReduction.ParRoutine

namespace MIPRE.AnswerReduction
noncomputable section
open Cost Cost.PolyTimeFun CL CL.Detyping.Program Pipeline SAT Pcp StageProg ParRoutine
theorem stg_runs (arg : PolyTimeFun Data Data) {p : Prog} (hp : p.WellScoped 1) (X r : Data)
    (h : ∃ t, p.Runs (arg X) r t) : ∃ t, (stg arg p).Runs X (.cons r X) t := by
  obtain ⟨t, ht⟩ := h
  obtain ⟨t', h'⟩ := stageProg_runs (ap₂ treePair arg (PolyTimeFun.id Data)) hp postKeep X
    (arg X) X r t (by simp) ht
  exact ⟨t', by simpa [postKeep, stg] using h'⟩
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
theorem descs_m : ((List.ofFn ((family PD lam mu sigma).desc n)).getD 0 default).2.1 =
    unary (arPar PD lam mu sigma n).m := by
  rw [show (0 : ℕ) = ((0 : Fin 6) : ℕ) from rfl, getD_desc, PcpFamily.desc_lt _ _ 0 (by decide)]
  rfl
end
end MIPRE.AnswerReduction

namespace MIPRE.AnswerReduction
noncomputable section
open Cost Cost.PolyTimeFun CL CL.Detyping.Program Pipeline SAT Pcp StageProg ParRoutine
variable (PD : PcpDecider) (ℓ : ℕ) (sp dp : Prog) (lam mu sigma n : ℕ) (u v : ArTy)
  (x y a b : BitStr)
variable (rxA rxB ryA ryB : Data)
theorem argPar_zero : argPar 0 (ctx0 sp dp lam mu sigma n u v x y a b) =
    .cons (encode (lam, mu, sigma)) (encode n) := by
  simp [argPar, lmsD, hdat, inp, ctx0, encode_prod]
end
end MIPRE.AnswerReduction

namespace MIPRE.AnswerReduction
noncomputable section
open Cost Cost.PolyTimeFun CL CL.Detyping.Program Pipeline SAT Pcp StageProg ParRoutine
variable (PD : PcpDecider) (ℓ : ℕ) (sp dp : Prog) (lam mu sigma n : ℕ) (u v : ArTy)
  (x y a b : BitStr)
variable (rxA rxB ryA ryB : Data)
theorem argPar_one : argPar 1 (ctx1 PD sp dp lam mu sigma n u v x y a b) =
    .cons (encode (lam, mu, sigma)) (encode n) := by
  simp [argPar, lmsD, hdat, inp, ctx1, ctx0, encode_prod]
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
theorem margArg_eq (j i : ℕ) (w : Player) (d : Data) (z : BitStr)
    (hpd : pdD j d = (family PD lam mu sigma).pd n) (hsp : spD j d = encode sp)
    (hn : inp j 0 d = encode n) (hz : inp j i d = encode z) :
    argMarg ℓ j i w d = margQ PD ℓ sp lam mu sigma n w z := by
  obtain ⟨-, -, hdim⟩ := pdD_eq PD lam mu sigma n d hpd
  simp only [argMarg, oBits, qBits, ap₂_apply, treePair_apply, comp_apply, pair_apply,
    const_apply, encoded_apply, hsp, hn, hz, readBits_encode, hdim, margQ, encode_prod]
  rfl
end
end MIPRE.AnswerReduction

namespace MIPRE.AnswerReduction
noncomputable section
open Cost Cost.PolyTimeFun CL CL.Detyping.Program Pipeline SAT Pcp StageProg ParRoutine
variable (PD : PcpDecider) (ℓ : ℕ) (sp dp : Prog) (lam mu sigma n : ℕ) (u v : ArTy)
  (x y a b : BitStr)
variable (rxA rxB ryA ryB : Data)
theorem aBlocks_eq (j it ia : ℕ) (d : Data) (t : ArTy) (s : BitStr)
    (hpd : pdD j d = (family PD lam mu sigma).pd n) (ht : inp j it d = encode t)
    (hs : (if ia = 5 then inp j ia else inpLast j) d = encode s) :
    aBlocks j it ia d = aBl PD lam mu sigma n t s := by
  obtain ⟨hk, -, -⟩ := pdD_eq PD lam mu sigma n d hpd
  obtain ⟨-, hm', hds⟩ := pd_heads PD lam mu sigma n
  have hs' : readBits ((if ia = 5 then inp j ia else inpLast j) d) = s := by
    rw [hs, readBits_encode]
  simp only [aBlocks, comp_apply, pair_apply, snd_apply, fst_apply, const_apply, hk,
    SAT.ArrayProg.getD_apply, map_apply, hpd, hds, descs_m, ht, readFinite_encode, cntP_apply,
    length_unary, hs', aBl]
  simp only [m'D, comp_apply, hpd, hm', length_unary]
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
theorem argVer_eq (j i it ia rA rB : ℕ) (d RA RB : Data) (z : BitStr) (t : ArTy) (s : BitStr)
    (hpd : pdD j d = (family PD lam mu sigma).pd n) (hdp : dpD j d = encode dp)
    (hn : inp j 0 d = encode n)
    (hqt : res (j - 2) d = encode (arQ lam mu n, tPcp lam mu n))
    (hσ : treeTail (treeTail (lmsD j d)) = encode sigma) (hA : res rA d = RA) (hB : res rB d = RB)
    (hz : inp j i d = encode z) (ht : inp j it d = encode t)
    (hs : (if ia = 5 then inp j ia else inpLast j) d = encode s) :
    argVer j i it ia rA rB d = encode (pcpInput dp n (tPcp lam mu n)
      (arQ lam mu n) sigma (readBits RA) (readBits RB) (pBl PD lam mu sigma n z).1
      (aBl PD lam mu sigma n t s)) := by
  rw [argVer]
  simp only [ap₂_apply, treePair_apply, comp_apply, encoded_apply, hdp, hn, hqt, hσ, hA, hB,
    readNat_encode, encode_prod, treeHead_cons, treeTail_cons,
    pBlocks_eq PD lam mu sigma n j i d z hpd hz, aBlocks_eq PD lam mu sigma n j it ia d t s hpd ht hs,
    fst_apply, pcpInput]
end
end MIPRE.AnswerReduction

namespace MIPRE.AnswerReduction
noncomputable section
open Cost Cost.PolyTimeFun CL CL.Detyping.Program Pipeline SAT Pcp StageProg ParRoutine
variable (PD : PcpDecider) (ℓ : ℕ) (sp dp : Prog) (lam mu sigma n : ℕ) (u v : ArTy)
  (x y a b : BitStr)
variable (rxA rxB ryA ryB : Data)
theorem ctx6_reads :
    pdD 6 (ctx6 PD sp dp lam mu sigma n u v x y a b rxA rxB ryA ryB) = (family PD lam mu sigma).pd n ∧
    dpD 6 (ctx6 PD sp dp lam mu sigma n u v x y a b rxA rxB ryA ryB) = encode dp ∧
    inp 6 0 (ctx6 PD sp dp lam mu sigma n u v x y a b rxA rxB ryA ryB) = encode n ∧
    res 4 (ctx6 PD sp dp lam mu sigma n u v x y a b rxA rxB ryA ryB) =
      encode (arQ lam mu n, tPcp lam mu n) ∧
    treeTail (treeTail (lmsD 6 (ctx6 PD sp dp lam mu sigma n u v x y a b rxA rxB ryA ryB))) =
      encode sigma ∧
    res 3 (ctx6 PD sp dp lam mu sigma n u v x y a b rxA rxB ryA ryB) = rxA ∧
    res 2 (ctx6 PD sp dp lam mu sigma n u v x y a b rxA rxB ryA ryB) = rxB ∧
    inp 6 2 (ctx6 PD sp dp lam mu sigma n u v x y a b rxA rxB ryA ryB) = encode x ∧
    inp 6 1 (ctx6 PD sp dp lam mu sigma n u v x y a b rxA rxB ryA ryB) = encode u ∧
    (if (5 : ℕ) = 5 then inp 6 5 else inpLast 6)
      (ctx6 PD sp dp lam mu sigma n u v x y a b rxA rxB ryA ryB) = encode a := by
  simp [pdD, res, dpD, hdat, inp, lmsD, ctx6, ctx2, ctx1, ctx0, encode_prod]
end
end MIPRE.AnswerReduction

namespace MIPRE.AnswerReduction
noncomputable section
open Cost Cost.PolyTimeFun CL CL.Detyping.Program Pipeline SAT Pcp StageProg ParRoutine
variable (PD : PcpDecider) (ℓ : ℕ) (sp dp : Prog) (lam mu sigma n : ℕ) (u v : ArTy)
  (x y a b : BitStr)
variable (rxA rxB ryA ryB : Data)
theorem ctx7_reads :
    pdD 7 (ctx7 PD sp dp lam mu sigma n u v x y a b rxA rxB ryA ryB) = (family PD lam mu sigma).pd n ∧
    dpD 7 (ctx7 PD sp dp lam mu sigma n u v x y a b rxA rxB ryA ryB) = encode dp ∧
    inp 7 0 (ctx7 PD sp dp lam mu sigma n u v x y a b rxA rxB ryA ryB) = encode n ∧
    res 5 (ctx7 PD sp dp lam mu sigma n u v x y a b rxA rxB ryA ryB) =
      encode (arQ lam mu n, tPcp lam mu n) ∧
    treeTail (treeTail (lmsD 7 (ctx7 PD sp dp lam mu sigma n u v x y a b rxA rxB ryA ryB))) =
      encode sigma ∧
    res 2 (ctx7 PD sp dp lam mu sigma n u v x y a b rxA rxB ryA ryB) = ryA ∧
    res 1 (ctx7 PD sp dp lam mu sigma n u v x y a b rxA rxB ryA ryB) = ryB ∧
    inp 7 4 (ctx7 PD sp dp lam mu sigma n u v x y a b rxA rxB ryA ryB) = encode y ∧
    inp 7 3 (ctx7 PD sp dp lam mu sigma n u v x y a b rxA rxB ryA ryB) = encode v ∧
    (if (6 : ℕ) = 5 then inp 7 6 else inpLast 7)
      (ctx7 PD sp dp lam mu sigma n u v x y a b rxA rxB ryA ryB) = encode b := by
  simp [pdD, res, dpD, hdat, inp, inpLast, lmsD, ctx7, ctx6, ctx2, ctx1, ctx0, encode_prod]
end
end MIPRE.AnswerReduction

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.AnswerReduction
open Cost Cost.PolyTimeFun CL CL.Detyping.Program Pipeline SAT Pcp StageProg ParRoutine
variable (PD : PcpDecider) (ℓ : ℕ) (sp dp : Prog) (lam mu sigma n : ℕ) (u v : ArTy)
  (x y a b : BitStr)
variable (rxA rxB ryA ryB : Data)
theorem _root_.solution
    (hxA : ∃ t, selfUniversal.univ.Runs (margQ PD ℓ sp lam mu sigma n .alice x) rxA t)
    (hxB : ∃ t, selfUniversal.univ.Runs (margQ PD ℓ sp lam mu sigma n .bob x) rxB t)
    (hyA : ∃ t, selfUniversal.univ.Runs (margQ PD ℓ sp lam mu sigma n .alice y) ryA t)
    (hyB : ∃ t, selfUniversal.univ.Runs (margQ PD ℓ sp lam mu sigma n .bob y) ryB t) :
    ∃ t, (core PD ℓ).Runs (ctx0 sp dp lam mu sigma n u v x y a b)
      (encode (verdictP (readV (ctx8 PD sp dp lam mu sigma n u v x y a b rxA rxB ryA ryB)))) t := by
  have hu := selfUniversal.closed
  have hv := PD.verify.closed
  set X0 := ctx0 sp dp lam mu sigma n u v x y a b
  set X2 := ctx2 PD sp dp lam mu sigma n u v x y a b
  have r1 := stg_runs (argPar 0) (ParRoutine.core_closed PD) X0 _
    (by rw [argPar_zero]; exact parCore_runs PD lam mu sigma n)
  have r2 := stg_runs (argPar 1) budCore_closed (ctx1 PD sp dp lam mu sigma n u v x y a b) _
    (by rw [argPar_one]; exact budCore_runs lam mu sigma n)
  have r3 := stg_runs (argMarg ℓ 2 2 .alice) hu X2 rxA (by
    rw [margArg_eq PD ℓ sp lam mu sigma n 2 2 .alice X2 x (by simp [pdD, res, X2, ctx2, ctx1])
      (by simp [spD, hdat, X2, ctx2, ctx1, ctx0, encode_prod])
      (by simp [inp, X2, ctx2, ctx1, ctx0, encode_prod])
      (by simp [inp, X2, ctx2, ctx1, ctx0, encode_prod])]
    exact hxA)
  have r4 := stg_runs (argMarg ℓ 3 2 .bob) hu (.cons rxA X2) rxB (by
    rw [margArg_eq PD ℓ sp lam mu sigma n 3 2 .bob _ x (by simp [pdD, res, X2, ctx2, ctx1])
      (by simp [spD, hdat, X2, ctx2, ctx1, ctx0, encode_prod])
      (by simp [inp, X2, ctx2, ctx1, ctx0, encode_prod])
      (by simp [inp, X2, ctx2, ctx1, ctx0, encode_prod])]
    exact hxB)
  have r5 := stg_runs (argMarg ℓ 4 4 .alice) hu (.cons rxB (.cons rxA X2)) ryA (by
    rw [margArg_eq PD ℓ sp lam mu sigma n 4 4 .alice _ y (by simp [pdD, res, X2, ctx2, ctx1])
      (by simp [spD, hdat, X2, ctx2, ctx1, ctx0, encode_prod])
      (by simp [inp, X2, ctx2, ctx1, ctx0, encode_prod])
      (by simp [inp, X2, ctx2, ctx1, ctx0, encode_prod])]
    exact hyA)
  have r6 := stg_runs (argMarg ℓ 5 4 .bob) hu (.cons ryA (.cons rxB (.cons rxA X2))) ryB (by
    rw [margArg_eq PD ℓ sp lam mu sigma n 5 4 .bob _ y (by simp [pdD, res, X2, ctx2, ctx1])
      (by simp [spD, hdat, X2, ctx2, ctx1, ctx0, encode_prod])
      (by simp [inp, X2, ctx2, ctx1, ctx0, encode_prod])
      (by simp [inp, X2, ctx2, ctx1, ctx0, encode_prod])]
    exact hyB)
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10⟩ :=
    ctx6_reads PD sp dp lam mu sigma n u v x y a b rxA rxB ryA ryB
  have r7 := stg_runs (argVer 6 2 1 5 3 2) hv (ctx6 PD sp dp lam mu sigma n u v x y a b rxA rxB
    ryA ryB) (encode (chkV PD dp lam mu sigma n rxA rxB x u a)) (by
      rw [argVer_eq PD dp lam mu sigma n 6 2 1 5 3 2 _ rxA rxB x u a e1 e2 e3 e4 e5 e6 e7 e8 e9 e10]
      obtain ⟨t, -, ht⟩ := PD.verify.computes (pcpInput dp n (tPcp lam mu n)
        (arQ lam mu n) sigma (readBits rxA) (readBits rxB) (pBl PD lam mu sigma n x).1
        (aBl PD lam mu sigma n u a))
      exact ⟨t, ht⟩)
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10⟩ :=
    ctx7_reads PD sp dp lam mu sigma n u v x y a b rxA rxB ryA ryB
  have r8 := stg_runs (argVer 7 4 3 6 2 1) hv (ctx7 PD sp dp lam mu sigma n u v x y a b rxA rxB
    ryA ryB) (encode (chkV PD dp lam mu sigma n ryA ryB y v b)) (by
      rw [argVer_eq PD dp lam mu sigma n 7 4 3 6 2 1 _ ryA ryB y v b f1 f2 f3 f4 f5 f6 f7 f8 f9 f10]
      obtain ⟨t, -, ht⟩ := PD.verify.computes (pcpInput dp n (tPcp lam mu n)
        (arQ lam mu n) sigma (readBits ryA) (readBits ryB) (pBl PD lam mu sigma n y).1
        (aBl PD lam mu sigma n v b))
      exact ⟨t, ht⟩)
  obtain ⟨t9, -, r9⟩ := (verdictP.comp readV).computes
    (ctx8 PD sp dp lam mu sigma n u v x y a b rxA rxB ryA ryB)
  have hc := PolyTimeFun.closed (verdictP.comp readV)
  exact seq_runs (seqProg_closed (stg_closed _ budCore_closed) <|
      seqProg_closed (stg_closed _ hu) <| seqProg_closed (stg_closed _ hu) <|
      seqProg_closed (stg_closed _ hu) <| seqProg_closed (stg_closed _ hu) <|
      seqProg_closed (stg_closed _ hv) <| seqProg_closed (stg_closed _ hv) hc) r1 <|
    seq_runs (seqProg_closed (stg_closed _ hu) <| seqProg_closed (stg_closed _ hu) <|
      seqProg_closed (stg_closed _ hu) <| seqProg_closed (stg_closed _ hu) <|
      seqProg_closed (stg_closed _ hv) <| seqProg_closed (stg_closed _ hv) hc) r2 <|
    seq_runs (seqProg_closed (stg_closed _ hu) <| seqProg_closed (stg_closed _ hu) <|
      seqProg_closed (stg_closed _ hu) <| seqProg_closed (stg_closed _ hv) <|
      seqProg_closed (stg_closed _ hv) hc) r3 <|
    seq_runs (seqProg_closed (stg_closed _ hu) <| seqProg_closed (stg_closed _ hu) <|
      seqProg_closed (stg_closed _ hv) <| seqProg_closed (stg_closed _ hv) hc) r4 <|
    seq_runs (seqProg_closed (stg_closed _ hu) <| seqProg_closed (stg_closed _ hv) <|
      seqProg_closed (stg_closed _ hv) hc) r5 <|
    seq_runs (seqProg_closed (stg_closed _ hv) <| seqProg_closed (stg_closed _ hv) hc) r6 <|
    seq_runs (seqProg_closed (stg_closed _ hv) hc) r7 <|
    seq_runs hc r8 ⟨t9, r9⟩
end MIPRE.AnswerReduction
