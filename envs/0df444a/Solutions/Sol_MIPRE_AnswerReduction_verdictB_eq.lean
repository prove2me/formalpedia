-- Prove2me | solution 1 for MIPRE.AnswerReduction.verdictB_eq
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T06:33:01.841478+00:00
-- url     : https://prove2.me/submissions/860bf794-7fdb-4d39-96db-539c3da41ae1

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/AnswerReduction/DecideSpec.lean (solution of MIPRE.AnswerReduction.verdictB_eq);
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
import Theorems.Thm_MIPRE_AnswerReduction_ofElems_elems
import Theorems.Thm_MIPRE_AnswerReduction_sideB_eq
import Theorems.Thm_MIPRE_SAT_shoupBinField_toBits_ofBits

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.AnswerReduction
noncomputable section
open Finset MIPRE.LIDT MIPRE.LIDT.CL SAT Pcp Cost
variable {P : PcpParams} {k : ℕ} (E : BinField k)
/-- An answer parsed at the type `t` has the right format. -/
theorem ansFmt_of_parse {t : PcpTy} {s : BitStr} {a : Ans P E.carrier}
    (h : parse E t s = some a) : ansFmt t a = true := by
  unfold parse at h
  split at h
  · split_ifs at h
    obtain ⟨i, τ⟩ := t
    cases h
    by_cases hi : (i : ℕ) < 5 <;> cases τ <;> simp [ofElems, ansFmt, tyFmt, hi] <;> omega
  · cases h
end
end MIPRE.AnswerReduction

namespace MIPRE.AnswerReduction
noncomputable section
open Finset MIPRE.CL SAT Pcp Cost StageProg Introspection.FieldLineCheck Introspection.FieldQuestionProgram Introspection.SeedProgram LIDT LIDT.CL
variable {k : ℕ} (hk : 1 ≤ k) {P : PcpParams}
theorem ofFn_getD (l : List ((shoupBinField k hk)).carrier) {N : ℕ} (hN : l.length = N) :
    List.ofFn (fun r : Fin N => l.getD r 0) = l := by
  subst hN
  apply List.ext_getElem
  · simp
  · intro j _ h
    simp [List.getD_eq_getElem?_getD]
end
end MIPRE.AnswerReduction

namespace MIPRE.AnswerReduction
noncomputable section
open Finset MIPRE.CL SAT Pcp Cost StageProg Introspection.FieldLineCheck Introspection.FieldQuestionProgram Introspection.SeedProgram LIDT LIDT.CL
variable {k : ℕ} (hk : 1 ≤ k) {P : PcpParams}
theorem elems_ofElems (t : PcpTy) (l : List ((shoupBinField k hk)).carrier) (hl : l.length = cnt P t) :
    elems ((shoupBinField k hk)) (ofElems (P := P) ((shoupBinField k hk)) t l) = l := by
  obtain ⟨i, τ⟩ := t
  unfold cnt at hl
  unfold ofElems
  split_ifs at hl ⊢ with hi
  · cases τ
    · obtain ⟨a, rfl⟩ := List.length_eq_one_iff.mp hl
      rfl
    · exact ofFn_getD hk l hl
    · exact ofFn_getD hk l hl
  · cases τ
    · exact ofFn_getD hk l hl
    · change List.ofFn (fun r => l.getD (finProdFinEquiv (finProdFinEquiv.symm r)) 0) = l
      simp only [Equiv.apply_symm_apply]
      exact ofFn_getD hk l hl
    · change List.ofFn (fun r => l.getD (finProdFinEquiv (finProdFinEquiv.symm r)) 0) = l
      simp only [Equiv.apply_symm_apply]
      exact ofFn_getD hk l hl
end
end MIPRE.AnswerReduction

namespace MIPRE.AnswerReduction
noncomputable section
open Finset MIPRE.CL SAT Pcp Cost StageProg Introspection.FieldLineCheck Introspection.FieldQuestionProgram Introspection.SeedProgram LIDT LIDT.CL
variable {k : ℕ} (hk : 1 ≤ k) {P : PcpParams}
theorem ansB_injective {t : PcpTy} {u v : Ans P ((shoupBinField k hk)).carrier} (hu : ansFmt t u = true)
    (hv : ansFmt t v = true) (h : ansB hk u = ansB hk v) : u = v := by
  rw [← ofElems_elems ((shoupBinField k hk)) hu, ← ofElems_elems ((shoupBinField k hk)) hv]
  congr 1
  have := congrArg (List.map ((shoupBinField k hk)).ofBits) h
  simpa only [ansB, List.map_map, Function.comp_def, ((shoupBinField k hk)).ofBits_toBits, List.map_id'] using this
end
end MIPRE.AnswerReduction

namespace MIPRE.AnswerReduction
noncomputable section
open Finset MIPRE.CL SAT Pcp Cost StageProg Introspection.FieldLineCheck Introspection.FieldQuestionProgram Introspection.SeedProgram LIDT LIDT.CL
variable {k : ℕ} (hk : 1 ≤ k) {P : PcpParams}
theorem ansB_ofElems (t : PcpTy) (bs : List BitStr) (hl : bs.length = cnt P t)
    (hw : ∀ b ∈ bs, b.length = k) :
    ansB hk (ofElems (P := P) ((shoupBinField k hk)) t (bs.map ((shoupBinField k hk)).ofBits)) = bs := by
  rw [ansB, elems_ofElems hk t _ (by simp [hl]), List.map_map]
  conv_rhs => rw [← List.map_id bs]
  apply List.map_congr_left
  intro b hb
  exact shoupBinField_toBits_ofBits k hk b (hw b hb)
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

namespace MIPRE.AnswerReduction
noncomputable section
open Finset MIPRE.CL SAT Pcp Cost StageProg Introspection.FieldLineCheck Introspection.FieldQuestionProgram Introspection.SeedProgram LIDT LIDT.CL
theorem cnt_eq (P : PcpParams) (t : PcpTy) : cnt P t = cntB P.m P.m' t := rfl
end
end MIPRE.AnswerReduction

namespace MIPRE.AnswerReduction
noncomputable section
open Finset MIPRE.CL SAT Pcp Cost StageProg Introspection.FieldLineCheck Introspection.FieldQuestionProgram Introspection.SeedProgram LIDT LIDT.CL
theorem parse_eq {k : ℕ} (E : BinField k) {P : PcpParams} (t : PcpTy) (s : BitStr) :
    parse (P := P) E t s = (parseB k (cnt P t) s).map fun bs => ofElems E t (bs.map E.ofBits) := by
  unfold parse parseB
  rcases (decode (Data.parse s) : Option (List BitStr)) with _ | bs
  · rfl
  · dsimp only
    split_ifs <;> rfl
end
end MIPRE.AnswerReduction

namespace MIPRE.AnswerReduction
noncomputable section
open Finset MIPRE.CL SAT Pcp Cost StageProg Introspection.FieldLineCheck Introspection.FieldQuestionProgram Introspection.SeedProgram LIDT LIDT.CL
theorem parseB_spec {k c : ℕ} {s : BitStr} {bs : List BitStr} (h : parseB k c s = some bs) :
    bs.length = c ∧ ∀ b ∈ bs, b.length = k := by
  unfold parseB at h
  split at h
  · split_ifs at h with hc
    cases h
    exact hc
  · cases h
end
end MIPRE.AnswerReduction

namespace MIPRE.AnswerReduction
noncomputable section
open Finset MIPRE.CL SAT Pcp Cost StageProg Introspection.FieldLineCheck Introspection.FieldQuestionProgram Introspection.SeedProgram LIDT LIDT.CL
variable (F : PcpFamily) (n : ℕ) {X : Type*}
  (check : X → (Fin (F.par n).m' → Fq (F.par n) (F.hk n)) →
    (Fin ((F.par n).m' + 6) → Fq (F.par n) (F.hk n)) → Bool)
theorem desc_zero_sz : ((List.ofFn (F.desc n)).getD 0 default).2.1.length = (F.par n).m := by
  rw [show (0 : ℕ) = ((0 : Fin 6) : ℕ) from rfl, getD_desc, F.desc_lt n 0 (by decide)]
  exact length_unary _
end
end MIPRE.AnswerReduction

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.AnswerReduction
open Finset MIPRE.CL SAT Pcp Cost StageProg Introspection.FieldLineCheck Introspection.FieldQuestionProgram Introspection.SeedProgram LIDT LIDT.CL
variable (F : PcpFamily) (n : ℕ) {X : Type*}
  (check : X → (Fin (F.par n).m' → Fq (F.par n) (F.hk n)) →
    (Fin ((F.par n).m' + 6) → Fq (F.par n) (F.hk n)) → Bool)
theorem _root_.solution (p q : Q (F.par n) (Fq (F.par n) (F.hk n)) X) (a b : BitStr)
    (chkP chkQ : Bool)
    (hP : ∀ u, parse (fld (F.par n) (F.hk n)) p.1.2 a = some u → chkPlan p.1 = true →
      chkP = check p.2.1 ((regs6 (F.par n)).ptOf p.2.2) (vals6 u))
    (hQ : ∀ v, parse (fld (F.par n) (F.hk n)) q.1.2 b = some v → chkPlan q.1 = true →
      chkQ = check q.2.1 ((regs6 (F.par n)).ptOf q.2.2) (vals6 v)) :
    verdictB (unary (F.par n).k) (unary (F.par n).m') (List.ofFn (F.desc n)) chkP chkQ p.1 q.1
        (blocksV (F.hk n) (F.par n) p.2.2) (blocksV (F.hk n) (F.par n) q.2.2) a b =
      match parse (fld (F.par n) (F.hk n)) p.1.2 a, parse (fld (F.par n) (F.hk n)) q.1.2 b with
      | some u, some v => accepts (F.sel n) (F.sel' n) check p q u v
      | _, _ => false := by
  simp only [verdictB, desc_zero_sz, length_unary, ← cnt_eq, parse_eq]
  rcases hA : parseB (F.par n).k (cnt (F.par n) p.1.2) a with _ | A <;>
    rcases hB : parseB (F.par n).k (cnt (F.par n) q.1.2) b with _ | B <;>
    simp only [Option.map_none, Option.map_some]
  obtain ⟨hAl, hAw⟩ := parseB_spec hA
  obtain ⟨hBl, hBw⟩ := parseB_spec hB
  set u := ofElems (P := F.par n) (fld (F.par n) (F.hk n)) p.1.2
    (A.map (fld (F.par n) (F.hk n)).ofBits)
  set v := ofElems (P := F.par n) (fld (F.par n) (F.hk n)) q.1.2
    (B.map (fld (F.par n) (F.hk n)).ofBits)
  have hpu : parse (fld (F.par n) (F.hk n)) p.1.2 a = some u := by rw [parse_eq, hA]; rfl
  have hqv : parse (fld (F.par n) (F.hk n)) q.1.2 b = some v := by rw [parse_eq, hB]; rfl
  have hu := ansFmt_of_parse _ hpu
  have hv := ansFmt_of_parse _ hqv
  have hAu : ansB (F.hk n) u = A := ansB_ofElems (F.hk n) _ A hAl hAw
  have hBv : ansB (F.hk n) v = B := ansB_ofElems (F.hk n) _ B hBl hBw
  rw [← hAu, ← hBv, acceptsB, accepts, hu, hv, Bool.true_and, Bool.true_and,
    sideB_eq F n check p q u v hu hv chkP (hP u hpu),
    sideB_eq F n check q p v u hv hu chkQ (hQ v hqv)]
  congr 2
  split_ifs with he
  · have he' : p.1.2 = q.1.2 := congrArg Prod.snd he
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    constructor
    · intro h
      exact ansB_injective (F.hk n) hu (he' ▸ hv) h
    · intro h
      rw [h]
  · rfl
end MIPRE.AnswerReduction
