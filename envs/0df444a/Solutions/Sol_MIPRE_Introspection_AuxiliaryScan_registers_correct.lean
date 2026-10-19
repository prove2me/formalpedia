-- Prove2me | solution 1 for MIPRE.Introspection.AuxiliaryScan.registers_correct
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T04:59:35.973782+00:00
-- url     : https://prove2.me/submissions/c494a7ea-716d-40b7-b4e8-f68417b0d427

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/AuxiliaryRegisterProgram.lean (solution of MIPRE.Introspection.AuxiliaryScan.registers_correct);
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
import Definitions.Def_MIPRE_Foundations_Introspection_AuxiliarySourceQueries
import Definitions.Def_MIPRE_Foundations_Introspection_AuxiliaryScanStage
import Definitions.Def_MIPRE_Foundations_Introspection_AuxiliaryScanProgram
import Definitions.Def_MIPRE_Foundations_Introspection_AuxiliaryScanCorrect
import Definitions.Def_MIPRE_Foundations_Introspection_AuxiliaryRegisterProgram
import Theorems.Thm_MIPRE_Introspection_AuxiliaryScan_program_complete
import Theorems.Thm_MIPRE_Introspection_AuxiliaryScan_program_sound
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
/-- Passing one stage adds exactly its selected register to the prefix. -/
theorem prefixRegister_step (P : CL.CLFun F ι ℓ) (k : ℕ) (y : ι → F) :
    prefixRegister P (k + 1) y = prefixRegister P k y ∪ P.factorOfPrefix k y := by
  induction P generalizing k y with
  | zero => cases k <;> simp [prefixRegister]
  | cons S L next ih =>
    cases k with
    | zero => simp [prefixRegister]
    | succ k =>
      simp only [prefixRegister, CL.CLFun.factorOfPrefix_cons_succ, ih]
      exact (union_assoc _ _ _).symm
end
end MIPRE.Introspection.CLChecks

namespace MIPRE.Introspection.AuxiliaryScan
noncomputable section
open Cost Cost.PolyTimeFun
theorem zeros_toBits {n : ℕ} (y : Fin n → CL.𝔽₂) :
    zeros (CL.toBits y) = CL.toBits (0 : Fin n → CL.𝔽₂) := by
  change (CL.toBits y).map (fun _ => false) = _
  simp [CL.toBits]
end
end MIPRE.Introspection.AuxiliaryScan

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
theorem unionMask_correct {n : ℕ} (S T : Finset (Fin n)) :
    unionMask (CL.indicatorBits S, CL.indicatorBits T) = CL.indicatorBits (S ∪ T) := by
  change ((CL.indicatorBits S).zip (CL.indicatorBits T)).map
    (fun p => if p.1 then true else p.2) = _
  apply List.ext_getElem
  · simp [CL.indicatorBits]
  · intro i hi hj
    simp only [CL.indicatorBits, List.getElem_map, List.getElem_zip, List.getElem_ofFn]
    simp only [Finset.mem_union]
    by_cases h : (⟨i, by simpa [CL.indicatorBits] using hj⟩ : Fin n) ∈ S <;> simp [h]
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

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Introspection.AuxiliaryScan
open Cost Cost.PolyTimeFun CLChecks
theorem _root_.solution (f : PolyTimeFun AuxiliarySource.Context BitStr)
    (m : PolyTimeFun AuxiliarySource.Context (List BitStr)) (ctx : AuxiliarySource.Context)
    {n ℓ : ℕ} {P : CL.CLFun CL.𝔽₂ (Fin n) ℓ} {T : Finset (Fin n)} (hP : P.SupportedOn T)
    (y : Fin n → CL.𝔽₂) (k : ℕ) (hq : ∀ j < k, QueriesCorrectAt f m ctx P j)
    (ha : ∃ x, (P.truncate (k - 1)).eval x = P.outputPrefix (k - 1) y) :
    registers f m k (ctx, CL.toBits y) = CL.indicatorBits (prefixRegister P k y) := by
  induction k with
  | zero =>
    change zeros (CL.toBits y) = CL.indicatorBits (prefixRegister P 0 y)
    rw [zeros_toBits]
    cases P <;> simp [CL.toBits, CL.indicatorBits, prefixRegister]
  | succ k ih =>
    have ha' : ∃ x, (P.truncate k).eval x = P.outputPrefix k y := by simpa using ha
    have he : ∃ x, (P.truncate (k - 1)).eval x = P.outputPrefix (k - 1) y := by
      obtain ⟨x, hx⟩ := ha'
      exact ⟨x, earlier_attained hP (by omega) y x hx⟩
    change unionMask (registers f m k (ctx, CL.toBits y), factorAt f m k (ctx, CL.toBits y)) = _
    rw [ih (fun j hj => hq j (by omega)) he,
      factorAt_correct f m ctx hP y k (fun j hj => hq j (by omega)) ha',
      unionMask_correct, prefixRegister_step]
end MIPRE.Introspection.AuxiliaryScan
