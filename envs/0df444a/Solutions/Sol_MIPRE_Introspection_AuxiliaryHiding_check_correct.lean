-- Prove2me | solution 1 for MIPRE.Introspection.AuxiliaryHiding.check_correct
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T05:02:50.600794+00:00
-- url     : https://prove2.me/submissions/dabd3a22-9b54-41a8-a30f-709272b6d3cc

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/AuxiliaryHidingNextProgram.lean (solution of MIPRE.Introspection.AuxiliaryHiding.check_correct);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Computability.Primrec.List
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Finset.Image
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.List.Basic
import Mathlib.Data.List.OfFn
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Pi
import Mathlib.Logic.Denumerable
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Function.Iterate
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Canonical
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_SAT_Circuit
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_CL_Closure_B
import Definitions.Def_MIPRE_Foundations_CL_Sampler
import Definitions.Def_MIPRE_Foundations_Verifier
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Fold
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_Closeness
import Definitions.Def_MIPRE_Foundations_PerfectStrategy
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_Foundations_GameDouble
import Definitions.Def_MIPRE_Foundations_OpBound
import Definitions.Def_MIPRE_Foundations_OpBound_B
import Definitions.Def_MIPRE_Foundations_StateDistance
import Definitions.Def_MIPRE_Foundations_StateDistance_B
import Definitions.Def_MIPRE_Foundations_POVMValue
import Definitions.Def_MIPRE_Foundations_Sign
import Definitions.Def_MIPRE_Foundations_CrossConsistency
import Definitions.Def_MIPRE_Foundations_CrossConsistency_B
import Definitions.Def_MIPRE_Foundations_PVM
import Definitions.Def_MIPRE_Foundations_PVM_B
import Definitions.Def_MIPRE_Foundations_Commutation
import Definitions.Def_MIPRE_Foundations_Dilation
import Definitions.Def_MIPRE_Foundations_Expanded
import Definitions.Def_MIPRE_Foundations_LowDegree_SchwartzZippel
import Definitions.Def_MIPRE_Foundations_LowDegree_Anticomm
import Definitions.Def_MIPRE_Foundations_Weyl
import Definitions.Def_MIPRE_Foundations_Parseval
import Definitions.Def_MIPRE_Foundations_Linearity
import Definitions.Def_MIPRE_Foundations_Sandwich
import Definitions.Def_MIPRE_Foundations_Pasting
import Definitions.Def_MIPRE_Foundations_GameAdapt
import Definitions.Def_MIPRE_Foundations_CL_Embedding
import Definitions.Def_MIPRE_Foundations_CL_Graph
import Definitions.Def_MIPRE_Foundations_CL_Detyping
import Definitions.Def_MIPRE_Foundations_CL_DetypingLaw
import Definitions.Def_MIPRE_Foundations_SampledGame
import Definitions.Def_MIPRE_Foundations_CL_DetypingGame
import Definitions.Def_MIPRE_Foundations_GapCompression
import Definitions.Def_MIPRE_Foundations_Cost_Codable_B
import Definitions.Def_MIPRE_Foundations_Halting_Descriptions
import Definitions.Def_MIPRE_Foundations_CL_TypedSampler
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryRepresentation
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryPolynomial
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
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryKernel
import Definitions.Def_MIPRE_Foundations_Cost_BinaryArithmetic
import Definitions.Def_MIPRE_Foundations_Cost_BinaryCompare
import Definitions.Def_MIPRE_Foundations_Cost_TreeBits
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgFinite
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgParse
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
import Definitions.Def_MIPRE_Foundations_Halting_Lists_B
import Definitions.Def_MIPRE_Foundations_Cost_Growth
import Definitions.Def_MIPRE_Foundations_Halting_Arith
import Definitions.Def_MIPRE_Foundations_Halting_Arith_B
import Definitions.Def_MIPRE_Foundations_VerifierValue
import Definitions.Def_MIPRE_Foundations_Pipeline_Budget
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgQueries
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgSampler
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgCost
import Definitions.Def_MIPRE_Foundations_CL_DetypingDeciderRoute
import Definitions.Def_MIPRE_Foundations_CL_DetypingDeciderProg
import Definitions.Def_MIPRE_Foundations_CL_DetypingClock
import Definitions.Def_MIPRE_Foundations_Pipeline_Introspection
import Definitions.Def_MIPRE_Foundations_Halting_PolyBounded
import Definitions.Def_MIPRE_Foundations_Introspection_ClockArithmetic
import Definitions.Def_MIPRE_Foundations_Introspection_ParserBits
import Definitions.Def_MIPRE_Foundations_Introspection_ParserAnswers
import Definitions.Def_MIPRE_Foundations_Introspection_DynamicParserSlice
import Definitions.Def_MIPRE_Foundations_Introspection_DynamicParser
import Definitions.Def_MIPRE_Foundations_Introspection_Clock
import Definitions.Def_MIPRE_Foundations_Introspection_ClockCost
import Definitions.Def_MIPRE_Foundations_Introspection_ClockSimulation
import Definitions.Def_MIPRE_Foundations_Introspection_SourceCompilerGuard
import Definitions.Def_MIPRE_Foundations_WeylEPR
import Definitions.Def_MIPRE_Foundations_Introspection_Types
import Definitions.Def_MIPRE_Foundations_Introspection_SamplingPrefix
import Definitions.Def_MIPRE_Foundations_Introspection_TwirlDistance
import Definitions.Def_MIPRE_Foundations_Introspection_LinearMeasurement
import Definitions.Def_MIPRE_Foundations_Introspection_CommutatorParseval
import Definitions.Def_MIPRE_Foundations_Introspection_BlockTwirl
import Definitions.Def_MIPRE_Foundations_Introspection_BlockPOVM
import Definitions.Def_MIPRE_Foundations_Introspection_EPR
import Definitions.Def_MIPRE_Foundations_Introspection_BlockRetention
import Definitions.Def_MIPRE_Foundations_Introspection_PauliMixing
import Definitions.Def_MIPRE_Foundations_Introspection_RegisterTransport
import Definitions.Def_MIPRE_Foundations_Introspection_RegisterEPR
import Definitions.Def_MIPRE_Foundations_Introspection_RegisterMixing
import Definitions.Def_MIPRE_Foundations_Introspection_RegisterCoordinates
import Definitions.Def_MIPRE_Foundations_Introspection_AuxiliaryChecks
import Definitions.Def_MIPRE_Foundations_Introspection_TypedPredicate
import Definitions.Def_MIPRE_Foundations_Introspection_AuxiliaryReadProgram
import Definitions.Def_MIPRE_Foundations_Introspection_ClockedQueryProgram
import Definitions.Def_MIPRE_Foundations_Introspection_Readout
import Definitions.Def_MIPRE_Foundations_Introspection_FinalExtraction
import Definitions.Def_MIPRE_Foundations_Introspection_TypeGraph
import Definitions.Def_MIPRE_Foundations_Introspection_HonestCore
import Definitions.Def_MIPRE_Foundations_Introspection_ConditionalNormalizer
import Definitions.Def_MIPRE_Foundations_Introspection_HonestFirstHide
import Definitions.Def_MIPRE_Foundations_Introspection_HonestAdaptive
import Definitions.Def_MIPRE_Foundations_Introspection_HonestRead
import Definitions.Def_MIPRE_Foundations_Introspection_HonestXCoordinates
import Definitions.Def_MIPRE_Foundations_Introspection_HonestHidingStep
import Definitions.Def_MIPRE_Foundations_Introspection_HonestHiding
import Definitions.Def_MIPRE_Foundations_Introspection_HonestLabelSupport
import Definitions.Def_MIPRE_Foundations_Introspection_TypedPresentation
import Definitions.Def_MIPRE_Foundations_Introspection_TypedEstimates
import Definitions.Def_MIPRE_Foundations_Introspection_HidingRigidity
import Definitions.Def_MIPRE_Foundations_Introspection_HonestHidingChecks
import Definitions.Def_MIPRE_Foundations_Introspection_HonestHidingAcceptance
import Definitions.Def_MIPRE_Foundations_Introspection_HidingMaps
import Definitions.Def_MIPRE_Foundations_Introspection_ConditionalNormalizerIdeal
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptivePrefixFactor
import Definitions.Def_MIPRE_Foundations_Introspection_TypedPrefixChain
import Definitions.Def_MIPRE_Foundations_Introspection_ReadChainMaps
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptiveResidual
import Definitions.Def_MIPRE_Foundations_Introspection_AuxiliaryPrefixSolve
import Definitions.Def_MIPRE_Foundations_Introspection_AuxiliaryMaskProgram
import Definitions.Def_MIPRE_Foundations_Introspection_AuxiliaryCanonicalProgram
import Definitions.Def_MIPRE_Foundations_Introspection_AuxiliaryDualProgram
import Definitions.Def_MIPRE_Foundations_Introspection_AuxiliaryDualKernel
import Definitions.Def_MIPRE_Foundations_Introspection_AuxiliaryQuotientProgram
import Definitions.Def_MIPRE_Foundations_Introspection_AuxiliaryDualDecode
import Definitions.Def_MIPRE_Foundations_Introspection_AuxiliaryQuotientChecks
import Definitions.Def_MIPRE_Foundations_Introspection_AuxiliaryHidingCoreProgram
import Definitions.Def_MIPRE_Foundations_Introspection_AuxiliarySourceQueries
import Definitions.Def_MIPRE_Foundations_Introspection_AuxiliaryScanStage
import Definitions.Def_MIPRE_Foundations_Introspection_AuxiliaryScanProgram
import Definitions.Def_MIPRE_Foundations_Introspection_AuxiliaryScanCorrect
import Definitions.Def_MIPRE_Foundations_Introspection_AuxiliaryRegisterProgram
import Definitions.Def_MIPRE_Foundations_Introspection_AuxiliaryHidingNextProgram
import Theorems.Thm_MIPRE_Introspection_AuxiliaryBits_quotient_correct
import Theorems.Thm_MIPRE_Introspection_AuxiliaryProgram_equal_iff
import Theorems.Thm_MIPRE_Introspection_AuxiliaryScan_program_complete
import Theorems.Thm_MIPRE_Introspection_AuxiliaryScan_program_sound
import Theorems.Thm_MIPRE_Introspection_AuxiliaryScan_registers_correct
import Theorems.Thm_MIPRE_Introspection_CLChecks_outputPrefix_outputPrefix
import Theorems.Thm_MIPRE_Introspection_CLChecks_proj_outputPrefix_cons

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.CL
section
variable {F : Type*} [Semiring F] {ι : Type*} [DecidableEq ι]
theorem proj_proj_of_disjoint {S T : Finset ι} (h : Disjoint S T) (x : ι → F) :
    proj S (proj T x) = 0 := by
  rw [proj_proj, Finset.disjoint_iff_inter_eq_empty.mp h, proj_empty]
end
end MIPRE.CL

namespace MIPRE.CL.RegLinear
section
variable {F : Type*} [Semiring F] {ι : Type*} [DecidableEq ι]
variable {S T : Finset ι}
theorem proj_apply_of_disjoint (L : RegLinear F S) (h : Disjoint T S) (x : ι → F) :
    proj T (L x) = 0 := by
  rw [← L.proj_apply x, proj_proj_of_disjoint h]
end
end MIPRE.CL.RegLinear

namespace MIPRE.CL.RegLinear
section
variable {F : Type*} [Semiring F] {ι : Type*} [DecidableEq ι]
variable {S T : Finset ι}
theorem proj_compl_apply [Fintype ι] (L : RegLinear F S) (x : ι → F) : proj Sᶜ (L x) = 0 :=
  L.proj_apply_of_disjoint disjoint_compl_left x
end
end MIPRE.CL.RegLinear

namespace MIPRE.CL.CLFun
section
universe u v
variable {F : Type u} [Semiring F] {ι : Type v} [DecidableEq ι] {ℓ : ℕ}
theorem SupportedOn.lift {P : CLFun F ι ℓ} {T T' : Finset ι} (hP : P.SupportedOn T)
    (h : T' ⊆ T) : (P.lift T').SupportedOn T := by
  induction P generalizing T T' with
  | zero => exact ⟨h, fun _ => trivial⟩
  | cons S L₁ next ih =>
    obtain ⟨hS, hnext⟩ := hP
    exact ⟨hS, fun v => ih v (hnext v) (Finset.sdiff_subset_sdiff h (Finset.Subset.refl S))⟩
end
end MIPRE.CL.CLFun

namespace MIPRE.CL.CLFun
section
universe u v
variable {F : Type u} [Semiring F] {ι : Type v} [DecidableEq ι] {ℓ : ℕ}
/-- Item (1) of `lem:cl-kth`: the `k`-th marginal is a `k`-level CL function on the same space. -/
theorem SupportedOn.truncate {P : CLFun F ι ℓ} {T : Finset ι} (hP : P.SupportedOn T) (k : ℕ) :
    (P.truncate k).SupportedOn T := by
  induction k generalizing ℓ P T with
  | zero => trivial
  | succ k ih =>
    cases P with
    | zero => exact (ih (supportedOn_zero T)).lift (Finset.empty_subset T)
    | cons S L₁ next =>
      obtain ⟨hS, hnext⟩ := hP
      exact ⟨hS, fun v => ih (hnext v)⟩
end
end MIPRE.CL.CLFun

namespace MIPRE.CL.CLFun
section
universe u v
variable {F : Type u} [Semiring F] {ι : Type v} [DecidableEq ι] {ℓ : ℕ}
variable [Fintype ι]
/-- A presentation on `V_T` takes its values in `V_T`. -/
theorem SupportedOn.proj_eval {P : CLFun F ι ℓ} {T : Finset ι} (hP : P.SupportedOn T)
    (x : ι → F) : proj T (P.eval x) = P.eval x := by
  induction P generalizing T x with
  | zero => simp
  | cons S L₁ next ih =>
    obtain ⟨hS, hnext⟩ := hP
    simp only [eval_cons, map_add, L₁.proj_apply_of_subset hS]
    rw [← ih _ (hnext _) (proj Sᶜ x), proj_proj_of_subset' Finset.sdiff_subset]
end
end MIPRE.CL.CLFun

namespace MIPRE.CL.CLFun
section
universe u v
variable {F : Type u} [Semiring F] {ι : Type v} [DecidableEq ι] {ℓ : ℕ}
variable [Fintype ι]
theorem SupportedOn.proj_eval_of_subset {P : CLFun F ι ℓ} {T U : Finset ι} (hP : P.SupportedOn T)
    (h : T ⊆ U) (x : ι → F) : proj U (P.eval x) = P.eval x := by
  rw [← hP.proj_eval x, proj_proj_of_subset' h, hP.proj_eval]
end
end MIPRE.CL.CLFun

namespace MIPRE.CL.CLFun
section
universe u v
variable {F : Type u} [Semiring F] {ι : Type v} [DecidableEq ι] {ℓ : ℕ}
variable [Fintype ι]
theorem SupportedOn.proj_eval_of_disjoint {P : CLFun F ι ℓ} {T U : Finset ι}
    (hP : P.SupportedOn T) (h : Disjoint U T) (x : ι → F) : proj U (P.eval x) = 0 := by
  rw [← hP.proj_eval x, proj_proj_of_disjoint h]
end
end MIPRE.CL.CLFun

namespace MIPRE.CL.CLFun
section
universe u v
variable {F : Type u} [Semiring F] {ι : Type v} [DecidableEq ι] {ℓ : ℕ}
variable [Fintype ι]
/-- The two components of the prefix `L_{≤(k+1)}(x) = L₁ x + r` of a presentation
`cons S L₁ next` on `V_T`: `L₁ x` on `V_S`, and `r`, the prefix of the continuation, on
`V_{T \ S}`. -/
theorem SupportedOn.proj_eval_truncate_succ {S : Finset ι} {L₁ : RegLinear F S}
    {next : (ι → F) → CLFun F ι ℓ} {T : Finset ι} (hP : (cons S L₁ next).SupportedOn T)
    (k : ℕ) (x : ι → F) :
    proj S (((cons S L₁ next).truncate (k + 1)).eval x) = L₁ x ∧
      proj Sᶜ (((cons S L₁ next).truncate (k + 1)).eval x) =
        ((next (L₁ x)).truncate k).eval (proj Sᶜ x) := by
  obtain ⟨hS, hnext⟩ := hP
  have hr := (hnext (L₁ x)).truncate k
  have hsub : T \ S ⊆ Sᶜ := fun i hi => by
    simp only [Finset.mem_sdiff] at hi
    simpa using hi.2
  rw [truncate_succ_cons, eval_cons]
  constructor
  · rw [map_add, L₁.proj_apply, hr.proj_eval_of_disjoint Finset.disjoint_sdiff, add_zero]
  · rw [map_add, L₁.proj_compl_apply, zero_add, hr.proj_eval_of_subset hsub]
end
end MIPRE.CL.CLFun

namespace MIPRE.CL.CLFun
section
open Finset
variable {F ι : Type*} [Field F] [Fintype ι] [DecidableEq ι] {ℓ : ℕ}
/-- An honest output's first register and remainder recover the two construction branches. -/
theorem SupportedOn.proj_eval_cons {S T : Finset ι} {L : RegLinear F S}
    {next : (ι → F) → CLFun F ι ℓ} (hP : (cons S L next).SupportedOn T) (z : ι → F) :
    proj S ((cons S L next).eval z) = L z ∧
      proj Sᶜ ((cons S L next).eval z) = (next (L z)).eval (proj Sᶜ z) := by
  have h := hP.proj_eval_truncate_succ ℓ z
  simpa only [truncate_self] using h
end
end MIPRE.CL.CLFun

namespace MIPRE.CL.CLFun
section
open Finset
variable {F ι : Type*} [Field F] [Fintype ι] [DecidableEq ι] {ℓ : ℕ}
/-- The sampling check can compute the honest marginal from the complete claimed output. -/
theorem SupportedOn.outputPrefix_eval {P : CLFun F ι ℓ} {T : Finset ι}
    (hP : P.SupportedOn T) (k : ℕ) (z : ι → F) :
    P.outputPrefix k (P.eval z) = (P.truncate k).eval z := by
  induction P generalizing T k z with
  | zero => cases k <;> simp [outputPrefix]
  | cons S L next ih =>
    cases k with
    | zero => rfl
    | succ k =>
      obtain ⟨hfirst, hrest⟩ := hP.proj_eval_cons z
      rw [outputPrefix_cons, hfirst, hrest, truncate_succ_cons, eval_cons,
        ih _ (hP.2 _) k (proj Sᶜ z)]
end
end MIPRE.CL.CLFun

namespace MIPRE.Introspection.AuxiliaryProgram
noncomputable section
open Cost Cost.PolyTimeFun CL.Detyping.Program
open CL.Detyping.DeciderProgram (lengthNat lengthNat_apply)
open SourceCompiler (GuardInput inputQ inputR inputLeft inputRight leftParts rightParts readInput)
theorem andCheck_iff {α : Type*} [SizedEncoding α] (f g : PolyTimeFun α Bool) (x : α) :
    andCheck f g x = true ↔ f x = true ∧ g x = true := by
  simp only [andCheck, PolyTimeFun.ite_apply, const_apply]
  cases f x <;> simp
end
end MIPRE.Introspection.AuxiliaryProgram

namespace MIPRE.Introspection.AuxiliaryProgram
noncomputable section
open Cost Cost.PolyTimeFun CL.Detyping.Program
open CL.Detyping.DeciderProgram (lengthNat lengthNat_apply)
open SourceCompiler (GuardInput inputQ inputR inputLeft inputRight leftParts rightParts readInput)
theorem toBits_injective {Q : ℕ} : Function.Injective (@CL.toBits Q) := by
  intro x y h
  simpa only [CL.ofBits_toBits] using congrArg (CL.ofBits Q) h
end
end MIPRE.Introspection.AuxiliaryProgram

namespace MIPRE.Introspection.CLChecks
noncomputable section
open Finset Classical
set_option linter.unusedSectionVars false
variable {F ι : Type*} [Field F] [Fintype ι] [DecidableEq ι] {ℓ : ℕ}
theorem factorOfPrefix_outputPrefix {P : CL.CLFun F ι ℓ} {T : Finset ι}
    (hP : P.SupportedOn T) (k : ℕ) (y : ι → F) :
    P.factorOfPrefix k (P.outputPrefix k y) = P.factorOfPrefix k y := by
  induction P generalizing T k y with
  | zero => simp
  | cons S L next ih =>
    cases k with
    | zero => rfl
    | succ k =>
      obtain ⟨ha, hb⟩ := proj_outputPrefix_cons hP k y
      simp only [CL.CLFun.factorOfPrefix_cons_succ]
      rw [ha, hb, ih _ (hP.2 _) k _]
end
end MIPRE.Introspection.CLChecks

namespace MIPRE.Introspection.CLChecks
noncomputable section
open Finset Classical
set_option linter.unusedSectionVars false
variable {F ι : Type*} [Field F] [Fintype ι] [DecidableEq ι] {ℓ : ℕ}
theorem stageLinear_toLinearMap (P : CL.CLFun F ι ℓ) (k : ℕ) (y : ι → F) :
    (stageLinear P k y).toLinearMap = P.mapOfPrefix k y := by
  induction P generalizing k y with
  | zero => rfl
  | cons S L next ih =>
    cases k with
    | zero => rfl
    | succ k => exact ih _ k _
end
end MIPRE.Introspection.CLChecks

namespace MIPRE.Introspection.AuxiliaryPrefix
noncomputable section
open Finset CLChecks
variable {F ι : Type*} [Field F] [Fintype ι] [DecidableEq ι] {ℓ : ℕ}
theorem mapOfPrefix_outputPrefix {P : CL.CLFun F ι ℓ} {T : Finset ι}
    (hP : P.SupportedOn T) (k : ℕ) (y : ι → F) :
    P.mapOfPrefix k (P.outputPrefix k y) = P.mapOfPrefix k y := by
  induction P generalizing T k y with
  | zero => simp
  | cons S L next ih =>
    cases k with
    | zero => rfl
    | succ k =>
      obtain ⟨ha, hb⟩ := proj_outputPrefix_cons hP k y
      simp only [CL.CLFun.mapOfPrefix_cons_succ]
      rw [ha, hb, ih _ (hP.2 _) k _]
end
end MIPRE.Introspection.AuxiliaryPrefix

namespace MIPRE.Introspection.AuxiliaryBits
noncomputable section
open Cost Cost.PolyTimeFun LowDegree.BinaryLinear LowDegree.BinaryPolynomial
theorem mask_correct {n : ℕ} (S : Finset (Fin n)) (x : Fin n → CL.𝔽₂) :
    mask (CL.indicatorBits S, CL.toBits x) = CL.toBits (CL.proj S x) := by
  change ((CL.indicatorBits S).zip (CL.toBits x)).map
    (fun p => if p.1 then p.2 else false) = _
  apply List.ext_getElem
  · simp [CL.indicatorBits, CL.toBits]
  · intro i hi hj
    simp only [CL.indicatorBits, CL.toBits, List.getElem_map, List.getElem_zip,
      List.getElem_ofFn]
    by_cases h : (⟨i, by simpa [CL.toBits] using hj⟩ : Fin n) ∈ S
    · simp [CL.proj_apply, h]
    · simp [CL.proj_apply, h]
end
end MIPRE.Introspection.AuxiliaryBits

namespace MIPRE.Introspection.AuxiliaryBits
noncomputable section
open Cost Cost.PolyTimeFun LowDegree.BinaryLinear LowDegree.BinaryPolynomial
theorem complement_correct {n : ℕ} (S : Finset (Fin n)) :
    complement (CL.indicatorBits S) = CL.indicatorBits Sᶜ := by
  change (CL.indicatorBits S).map (fun b => if b then false else true) = _
  simp only [CL.indicatorBits, List.map_ofFn]
  apply congrArg List.ofFn
  funext i
  simp only [Function.comp_apply, Finset.mem_compl]
  by_cases h : i ∈ S <;> simp [h]
end
end MIPRE.Introspection.AuxiliaryBits

namespace MIPRE.Introspection.AuxiliaryHiding
noncomputable section
open Cost Cost.PolyTimeFun LowDegree.BinaryLinear
open AuxiliaryProgram (andCheck andCheck_iff equal equal_iff toBits_injective)
theorem core_correct {n ℓ : ℕ} (P : CL.CLFun CL.𝔽₂ (Fin n) ℓ) (k : ℕ)
    (y yp x z zp t : Fin n → CL.𝔽₂) :
    core ((CL.toBits (P.outputPrefix k y), CL.toBits (P.outputPrefix k z)),
      ((CL.toBits y, CL.toBits yp, CL.toBits x), (CL.toBits z, CL.toBits zp, CL.toBits t)),
      (CL.indicatorBits (CLChecks.prefixRegister P (k + 1) z),
       CL.indicatorBits (CLChecks.prefixRegister P (k + 2) z),
       CL.indicatorBits (P.factorOfPrefix (k + 1) z),
       matrixBits (LinearMap.toMatrix' (P.mapOfPrefix (k + 1) z)))) = true ↔
      AuxiliaryQuotient.hidingNext P k (y, yp, x) (z, zp, t) := by
  simp only [core, andCheck_iff, equal_iff, comp_apply, pair_apply, fst_apply, snd_apply,
    prefixes, answers, masks, visited, remaining, fresh, nextMatrix,
    leftDual, rightDual, leftTail, rightTail]
  rw [← CLChecks.stageLinear_toLinearMap P (k + 1) z, AuxiliaryBits.quotient_correct]
  simp only [AuxiliaryBits.complement_correct, AuxiliaryBits.mask_correct, toBits_injective.eq_iff]
  rfl
end
end MIPRE.Introspection.AuxiliaryHiding

namespace MIPRE.Introspection.AuxiliaryScan
noncomputable section
open Cost LowDegree.BinaryLinear CLChecks
variable {n ℓ : ℕ}
theorem earlier_attained {P : CL.CLFun CL.𝔽₂ (Fin n) ℓ} {T : Finset (Fin n)}
    (hP : P.SupportedOn T) {j k : ℕ} (hj : j ≤ k) (y x : Fin n → CL.𝔽₂)
    (hx : (P.truncate k).eval x = P.outputPrefix k y) :
    (P.truncate j).eval x = P.outputPrefix j y := by
  have he : P.outputPrefix k (P.eval x) = P.outputPrefix k y :=
    (hP.outputPrefix_eval k x).trans hx
  have h := congrArg (P.outputPrefix j) he
  rw [outputPrefix_outputPrefix hP _ hj, outputPrefix_outputPrefix hP _ hj,
    hP.outputPrefix_eval] at h
  exact h
end
end MIPRE.Introspection.AuxiliaryScan

namespace MIPRE.Introspection.AuxiliaryScan
noncomputable section
open Cost Cost.PolyTimeFun CLChecks
theorem factorAt_correct (f : PolyTimeFun AuxiliarySource.Context BitStr)
    (m : PolyTimeFun AuxiliarySource.Context (List BitStr)) (ctx : AuxiliarySource.Context)
    {n ℓ : ℕ} {P : CL.CLFun CL.𝔽₂ (Fin n) ℓ} {T : Finset (Fin n)} (hP : P.SupportedOn T)
    (y : Fin n → CL.𝔽₂) (k : ℕ) (hq : ∀ j ≤ k, QueriesCorrectAt f m ctx P j)
    (ha : ∃ x, (P.truncate k).eval x = P.outputPrefix k y) :
    factorAt f m k (ctx, CL.toBits y) = CL.indicatorBits (P.factorOfPrefix k y) := by
  have hp := program_complete f m ctx hP y k (fun j hj => hq j (by omega)) ha
  obtain ⟨x, he, hx⟩ := program_sound f m ctx hP y k (fun j hj => hq j (by omega)) hp
  have hf := (hq k le_rfl _ ⟨x, hx⟩).1
  rw [factorOfPrefix_outputPrefix hP] at hf
  simp only [factorAt, PolyTimeFun.ite_apply, comp_apply, pair_apply, id_apply, he, fst_apply, if_true]
  exact hf
end
end MIPRE.Introspection.AuxiliaryScan

namespace MIPRE.Introspection.AuxiliaryHiding
noncomputable section
open Cost Cost.PolyTimeFun CLChecks AuxiliaryScan LowDegree.BinaryLinear
open AuxiliaryProgram (andCheck andCheck_iff)
theorem prepare_correct (f : PolyTimeFun AuxiliarySource.Context BitStr)
    (m : PolyTimeFun AuxiliarySource.Context (List BitStr)) (ctx : AuxiliarySource.Context)
    {n ℓ : ℕ} {P : CL.CLFun CL.𝔽₂ (Fin n) ℓ} {T : Finset (Fin n)} (hP : P.SupportedOn T)
    (k : ℕ) (y yp x z zp t : Fin n → CL.𝔽₂)
    (hq : ∀ j ≤ k + 1, QueriesCorrectAt f m ctx P j)
    (hy : ∃ a, (P.truncate k).eval a = P.outputPrefix k y)
    (hz : ∃ a, (P.truncate (k + 1)).eval a = P.outputPrefix (k + 1) z) :
    prepare f m k (ctx, (CL.toBits y, CL.toBits yp, CL.toBits x),
        (CL.toBits z, CL.toBits zp, CL.toBits t)) =
      ((CL.toBits (P.outputPrefix k y), CL.toBits (P.outputPrefix k z)),
       ((CL.toBits y, CL.toBits yp, CL.toBits x), (CL.toBits z, CL.toBits zp, CL.toBits t)),
       (CL.indicatorBits (prefixRegister P (k + 1) z),
        CL.indicatorBits (prefixRegister P (k + 2) z),
        CL.indicatorBits (P.factorOfPrefix (k + 1) z),
        matrixBits (LinearMap.toMatrix' (P.mapOfPrefix (k + 1) z)))) := by
  have hz0 : ∃ a, (P.truncate k).eval a = P.outputPrefix k z := by
    obtain ⟨a, ha⟩ := hz
    exact ⟨a, earlier_attained hP (by omega) z a ha⟩
  obtain ⟨a, hls, _⟩ := program_sound f m ctx hP y k
    (fun j hj => hq j (by omega))
    (program_complete f m ctx hP y k (fun j hj => hq j (by omega)) hy)
  obtain ⟨b, hrs, _⟩ := program_sound f m ctx hP z k
    (fun j hj => hq j (by omega))
    (program_complete f m ctx hP z k (fun j hj => hq j (by omega)) hz0)
  obtain ⟨c, hrn, hc⟩ := program_sound f m ctx hP z (k + 1)
    (fun j hj => hq j (by omega))
    (program_complete f m ctx hP z (k + 1) (fun j hj => hq j (by omega)) hz)
  have hro := registers_correct f m ctx hP z (k + 1)
    (fun j hj => hq j (by omega)) (by simpa using hz0)
  have hrnew := registers_correct f m ctx hP z (k + 2)
    (fun j hj => hq j (by omega)) (by simpa using hz)
  have hrf := factorAt_correct f m ctx hP z (k + 1) hq hz
  have hrm := (hq (k + 1) le_rfl _ ⟨c, hc⟩).2
  rw [AuxiliaryPrefix.mapOfPrefix_outputPrefix hP] at hrm
  simp only [prepare, leftScan, rightScan, leftInput, rightInput, sourceContext,
    leftAnswer, rightAnswer, comp_apply, pair_apply, fst_apply, snd_apply,
    hls, hrs, hrn, hro, hrnew, hrf]
  change (_, _, _, _, _, m (contextAt ctx (k + 2) (CL.toBits (P.outputPrefix (k + 1) z)))) = _
  rw [hrm]
end
end MIPRE.Introspection.AuxiliaryHiding

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Introspection.AuxiliaryHiding
open Cost Cost.PolyTimeFun CLChecks AuxiliaryScan LowDegree.BinaryLinear
open AuxiliaryProgram (andCheck andCheck_iff)
theorem _root_.solution (f : PolyTimeFun AuxiliarySource.Context BitStr)
    (m : PolyTimeFun AuxiliarySource.Context (List BitStr)) (ctx : AuxiliarySource.Context)
    {n ℓ : ℕ} {P : CL.CLFun CL.𝔽₂ (Fin n) ℓ} {T : Finset (Fin n)} (hP : P.SupportedOn T)
    (k : ℕ) (y yp x z zp t : Fin n → CL.𝔽₂)
    (hq : ∀ j ≤ k + 1, QueriesCorrectAt f m ctx P j) :
    check f m k (ctx, (CL.toBits y, CL.toBits yp, CL.toBits x),
      (CL.toBits z, CL.toBits zp, CL.toBits t)) = true ↔
      (∃ a, (P.truncate k).eval a = P.outputPrefix k y) ∧
      (∃ a, (P.truncate (k + 1)).eval a = P.outputPrefix (k + 1) z) ∧
      AuxiliaryQuotient.hidingNext P k (y, yp, x) (z, zp, t) := by
  simp only [check, andCheck_iff, comp_apply, leftScan, rightScan, leftInput, rightInput,
    sourceContext, leftAnswer, rightAnswer, pair_apply, fst_apply, snd_apply]
  constructor
  · rintro ⟨hl, hr, hc⟩
    obtain ⟨a, _, ha⟩ := program_sound f m ctx hP y k (fun j hj => hq j (by omega)) hl
    obtain ⟨b, _, hb⟩ := program_sound f m ctx hP z (k + 1) (fun j hj => hq j (by omega)) hr
    refine ⟨⟨a, ha⟩, ⟨b, hb⟩, ?_⟩
    rw [prepare_correct f m ctx hP k y yp x z zp t hq ⟨a, ha⟩ ⟨b, hb⟩,
      core_correct] at hc
    exact hc
  · rintro ⟨hy, hz, hc⟩
    refine ⟨program_complete f m ctx hP y k (fun j hj => hq j (by omega)) hy,
      program_complete f m ctx hP z (k + 1) (fun j hj => hq j (by omega)) hz, ?_⟩
    rw [prepare_correct f m ctx hP k y yp x z zp t hq hy hz, core_correct]
    exact hc
end MIPRE.Introspection.AuxiliaryHiding
