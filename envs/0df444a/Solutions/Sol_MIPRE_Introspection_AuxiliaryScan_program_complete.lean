-- Prove2me | solution 1 for MIPRE.Introspection.AuxiliaryScan.program_complete
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T04:55:23.960888+00:00
-- url     : https://prove2.me/submissions/b83ca5f6-32ca-4610-a9ee-f5bc4a6a146c

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/AuxiliaryScanCorrect.lean (solution of MIPRE.Introspection.AuxiliaryScan.program_complete);
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
import Theorems.Thm_MIPRE_CL_CLFun_SupportedOn_eval_truncate_eq_sum
import Theorems.Thm_MIPRE_Introspection_AuxiliaryScan_program_sound
import Theorems.Thm_MIPRE_Introspection_AuxiliaryScan_stage_correct
import Theorems.Thm_MIPRE_Introspection_CLChecks_outputPrefix_outputPrefix
import Theorems.Thm_MIPRE_Introspection_CLChecks_proj_outputPrefix_cons
import Theorems.Thm_MIPRE_Introspection_CLChecks_proj_prefixRegister
import Theorems.Thm_MIPRE_Introspection_CLChecks_stageFactor_subset_residual
import Theorems.Thm_MIPRE_LowDegree_BinaryLinear_IsPivotBasis_append_reduced
import Theorems.Thm_MIPRE_LowDegree_BinaryLinear_IsPivotBasis_eq_zero_of_pivots_zero
import Theorems.Thm_MIPRE_LowDegree_BinaryLinear_binary_eq_zero_or_one
import Theorems.Thm_MIPRE_LowDegree_BinaryLinear_coordinateRows_matrixBits
import Theorems.Thm_MIPRE_LowDegree_BinaryLinear_getD_vectorBits
import Theorems.Thm_MIPRE_LowDegree_BinaryLinear_insertRow_pivotBits
import Theorems.Thm_MIPRE_LowDegree_BinaryLinear_typedBasis_span
import Theorems.Thm_MIPRE_LowDegree_BinaryLinear_typedReduceStep_error
import Theorems.Thm_MIPRE_LowDegree_BinaryLinear_xorBits_vectorBits

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

namespace MIPRE.CL
section
variable {F : Type*} [Semiring F] {ι : Type*} [DecidableEq ι]
theorem proj_union_of_disjoint {S T : Finset ι} (h : Disjoint S T) (x : ι → F) :
    proj (S ∪ T) x = proj S x + proj T x := by
  ext i
  by_cases hS : i ∈ S
  · have hT : i ∉ T := Finset.disjoint_left.mp h hS
    simp [hS, hT]
  · by_cases hT : i ∈ T <;> simp [hS, hT]
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
universe u v
variable {F : Type u} [Semiring F] {ι : Type v} [DecidableEq ι] {ℓ : ℕ}
variable [Fintype ι]
/-- The linear map at a stage is determined by the prefix: `mapOfPrefix` computes `mapAt`. -/
theorem SupportedOn.mapOfPrefix_eval {P : CLFun F ι ℓ} {T : Finset ι} (hP : P.SupportedOn T)
    (k : ℕ) (x : ι → F) : P.mapOfPrefix k ((P.truncate k).eval x) = P.mapAt k x := by
  induction P generalizing T k x with
  | zero => rfl
  | cons S L₁ next ih =>
    cases k with
    | zero => rfl
    | succ k =>
      obtain ⟨h₁, h₂⟩ := hP.proj_eval_truncate_succ k x
      rw [mapOfPrefix_cons_succ, h₁, h₂, mapAt_cons_succ]
      exact ih _ (hP.2 _) k _
end
end MIPRE.CL.CLFun

namespace MIPRE.LowDegree.BinaryLinear
section
open Cost Cost.PolyTimeFun Polynomial
/-- A raw XOR step is the corresponding operation on both typed vectors. -/
theorem reduceStep_rowBits {n t : ℕ} (r : Row n t) (p : Pivot n t) :
    reduceStep (rowBits r) (pivotBits p) = rowBits (typedReduceStep r p) := by
  unfold reduceStep pivotBits rowBits
  rw [getD_vectorBits]
  simp only [bit, decide_eq_true_eq, typedReduceStep]
  split_ifs
  · rw [xorBits_vectorBits, xorBits_vectorBits]
  · rfl
end
end MIPRE.LowDegree.BinaryLinear

namespace MIPRE.LowDegree.BinaryLinear
section
open Cost Cost.PolyTimeFun Polynomial
/-- The entire executable reduction agrees with typed binary elimination. -/
theorem reduceRows_rowBits {n t : ℕ} (b : List (Pivot n t)) (r : Row n t) :
    reduceRows (b.map pivotBits) (rowBits r) = rowBits (typedReduce b r) := by
  induction b generalizing r with
  | nil => rfl
  | cons p b ih =>
    change reduceRows (b.map pivotBits) (reduceStep (rowBits r) (pivotBits p)) = _
    rw [reduceStep_rowBits, ih]
    rfl
end
end MIPRE.LowDegree.BinaryLinear

namespace MIPRE.LowDegree.BinaryLinear
section
open Cost Cost.PolyTimeFun Polynomial
theorem represents_typedReduceStep {n t : ℕ}
    (L : (Fin t → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2))
    (r : Row n t) (p : Pivot n t) (hr : Represents L r) (hp : Represents L p.2) :
    Represents L (typedReduceStep r p) := by
  unfold typedReduceStep
  split
  · change L (r.2 + p.2.2) = r.1 + p.2.1
    rw [map_add, hr, hp]
  · exact hr
end
end MIPRE.LowDegree.BinaryLinear

namespace MIPRE.LowDegree.BinaryLinear
section
open Cost Cost.PolyTimeFun Polynomial
/-- Reduction preserves the coefficient certificate in the original family. -/
theorem represents_typedReduce {n t : ℕ}
    (L : (Fin t → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2))
    (b : List (Pivot n t)) (r : Row n t) (hr : Represents L r)
    (hb : ∀ p ∈ b, Represents L p.2) : Represents L (typedReduce b r) := by
  induction b generalizing r with
  | nil => exact hr
  | cons p b ih =>
    exact ih _ (represents_typedReduceStep L r p hr (hb p (by simp)))
      (fun q hq => hb q (by simp [hq]))
end
end MIPRE.LowDegree.BinaryLinear

namespace MIPRE.LowDegree.BinaryLinear
section
open Cost Cost.PolyTimeFun Polynomial
theorem firstOne_getD (v : BitStr) (h : firstOne v < v.length) :
    v.getD (firstOne v) false = true := by
  have hbit := List.findIdx_getElem (xs := v) (p := id) (w := h)
  change v[firstOne v]?.getD false = true
  rw [List.getElem?_eq_getElem h]
  exact hbit
end
end MIPRE.LowDegree.BinaryLinear

namespace MIPRE.LowDegree.BinaryLinear
section
variable {n t : ℕ}
attribute [local instance] MIPRE.LowDegree.BinaryLinear.instFactPrimeOfNatNat_mIPRE
theorem typedReduceStep_pivot_zero (r : Row n t) (p : Pivot n t)
    (hp : p.2.1 p.1 = 1) : (typedReduceStep r p).1 p.1 = 0 := by
  rcases binary_eq_zero_or_one (r.1 p.1) with h | h
  · simp [typedReduceStep, h]
  · simp only [typedReduceStep, h, if_true, Pi.add_apply, hp]
    decide
end
end MIPRE.LowDegree.BinaryLinear

namespace MIPRE.LowDegree.BinaryLinear
section
variable {n t : ℕ}
attribute [local instance] MIPRE.LowDegree.BinaryLinear.instFactPrimeOfNatNat_mIPRE
theorem typedReduceStep_preserves_zero (r : Row n t) (p : Pivot n t) (j : Fin n)
    (hr : r.1 j = 0) (hp : p.2.1 j = 0) : (typedReduceStep r p).1 j = 0 := by
  unfold typedReduceStep
  split <;> simp [hr, hp]
end
end MIPRE.LowDegree.BinaryLinear

namespace MIPRE.LowDegree.BinaryLinear
section
variable {n t : ℕ}
attribute [local instance] MIPRE.LowDegree.BinaryLinear.instFactPrimeOfNatNat_mIPRE
theorem typedReduce_preserves_zero (b : List (Pivot n t)) (r : Row n t) (j : Fin n)
    (hr : r.1 j = 0) (hb : ∀ p ∈ b, p.2.1 j = 0) : (typedReduce b r).1 j = 0 := by
  induction b generalizing r with
  | nil => exact hr
  | cons p b ih =>
    exact ih _ (typedReduceStep_preserves_zero r p j hr (hb p (by simp)))
      (fun q hq => hb q (by simp [hq]))
end
end MIPRE.LowDegree.BinaryLinear

namespace MIPRE.LowDegree.BinaryLinear
section
variable {n t : ℕ}
attribute [local instance] MIPRE.LowDegree.BinaryLinear.instFactPrimeOfNatNat_mIPRE
/-- Reducing against a triangular basis zeros all of its pivot coordinates. -/
theorem typedReduce_pivots_zero (b : List (Pivot n t)) (hb : IsPivotBasis b)
    (r : Row n t) : ∀ p ∈ b, (typedReduce b r).1 p.1 = 0 := by
  induction b generalizing r with
  | nil => simp
  | cons p b ih =>
    intro q hq
    rcases List.mem_cons.mp hq with hqp | hq
    · subst q
      exact typedReduce_preserves_zero b (typedReduceStep r p) p.1
        (typedReduceStep_pivot_zero r p hb.1) hb.2.1
    · exact ih hb.2.2 (typedReduceStep r p) q hq
end
end MIPRE.LowDegree.BinaryLinear

namespace MIPRE.LowDegree.BinaryLinear
section
variable {n t : ℕ}
theorem firstOne_vectorBits_one (v : Fin n → ZMod 2)
    (h : firstOne (vectorBits v) < n) : v ⟨firstOne (vectorBits v), h⟩ = 1 := by
  have hh := firstOne_getD (vectorBits v) (by simpa [vectorBits] using h)
  change (vectorBits v).getD (⟨firstOne (vectorBits v), h⟩ : Fin n) false = true at hh
  rw [getD_vectorBits] at hh
  simpa [bit] using hh
end
end MIPRE.LowDegree.BinaryLinear

namespace MIPRE.LowDegree.BinaryLinear
section
variable {n t : ℕ}
/-- Insertion maintains the triangular pivot invariant. -/
theorem IsPivotBasis.typedInsert {b : List (Pivot n t)} (hb : IsPivotBasis b) (r : Row n t) :
    IsPivotBasis (typedInsert b r) := by
  unfold MIPRE.LowDegree.BinaryLinear.typedInsert
  dsimp only
  split
  · rename_i h
    exact hb.append_reduced r _ (firstOne_vectorBits_one _ h)
  · exact hb
end
end MIPRE.LowDegree.BinaryLinear

namespace MIPRE.LowDegree.BinaryLinear
section
variable {n t : ℕ}
theorem fold_insertRow_pivotBits (rows : List (Row n t)) (b : List (Pivot n t)) :
    (rows.map rowBits).foldl insertRow (b.map pivotBits) =
      (rows.foldl typedInsert b).map pivotBits := by
  induction rows generalizing b with
  | nil => rfl
  | cons r rows ih =>
    simp only [List.map_cons, List.foldl_cons, insertRow_pivotBits, ih]
end
end MIPRE.LowDegree.BinaryLinear

namespace MIPRE.LowDegree.BinaryLinear
section
variable {n t : ℕ}
/-- The actual ambient program constructs precisely the typed binary basis. -/
theorem basisRowsProg_correct (rows : List (Row n t)) :
    basisRowsProg (rows.map rowBits) = (typedBasis rows).map pivotBits :=
  fold_insertRow_pivotBits rows []
end
end MIPRE.LowDegree.BinaryLinear

namespace MIPRE.LowDegree.BinaryLinear
section
variable {n t : ℕ}
theorem fold_typedInsert_isPivotBasis (rows : List (Row n t)) (b : List (Pivot n t))
    (hb : IsPivotBasis b) : IsPivotBasis (rows.foldl typedInsert b) := by
  induction rows generalizing b with
  | nil => exact hb
  | cons r rows ih => exact ih _ (hb.typedInsert r)
end
end MIPRE.LowDegree.BinaryLinear

namespace MIPRE.LowDegree.BinaryLinear
section
variable {n t : ℕ}
theorem typedBasis_isPivotBasis (rows : List (Row n t)) : IsPivotBasis (typedBasis rows) :=
  fold_typedInsert_isPivotBasis rows [] trivial
end
end MIPRE.LowDegree.BinaryLinear

namespace MIPRE.LowDegree.BinaryLinear
section
variable {n t : ℕ}
/-- Adding a stored vector preserves membership in every subspace containing it. -/
theorem typedReduceStep_mem_iff (S : Submodule (ZMod 2) (Fin n → ZMod 2))
    (r : Row n t) (p : Pivot n t) (hp : p.2.1 ∈ S) :
    (typedReduceStep r p).1 ∈ S ↔ r.1 ∈ S := by
  unfold typedReduceStep
  split
  · constructor
    · intro h
      have hs := S.sub_mem h hp
      simpa using hs
    · intro h
      exact S.add_mem h hp
  · rfl
end
end MIPRE.LowDegree.BinaryLinear

namespace MIPRE.LowDegree.BinaryLinear
section
variable {n t : ℕ}
theorem typedReduce_mem_iff (S : Submodule (ZMod 2) (Fin n → ZMod 2))
    (b : List (Pivot n t)) (r : Row n t) (hb : ∀ p ∈ b, p.2.1 ∈ S) :
    (typedReduce b r).1 ∈ S ↔ r.1 ∈ S := by
  induction b generalizing r with
  | nil => rfl
  | cons p b ih =>
    change (typedReduce b (typedReduceStep r p)).1 ∈ S ↔ _
    rw [ih _ (fun q hq => hb q (by simp [hq])),
      typedReduceStep_mem_iff S r p (hb p (by simp))]
end
end MIPRE.LowDegree.BinaryLinear

namespace MIPRE.LowDegree.BinaryLinear
section
open Cost Cost.PolyTimeFun
variable {n t : ℕ}
/-- A member of the basis span reduces to zero. -/
theorem IsPivotBasis.reduce_eq_zero {b : List (Pivot n t)} (hb : IsPivotBasis b)
    (r : Row n t) (hr : r.1 ∈ pivotSpan b) : (typedReduce b r).1 = 0 := by
  apply hb.eq_zero_of_pivots_zero _ _ (typedReduce_pivots_zero b hb r)
  apply (typedReduce_mem_iff (pivotSpan b) b r _).mpr hr
  intro p hp
  exact Submodule.subset_span ⟨p, hp, rfl⟩
end
end MIPRE.LowDegree.BinaryLinear

namespace MIPRE.LowDegree.BinaryLinear
section
open Cost Cost.PolyTimeFun
variable {n t : ℕ}
theorem represents_typedInsert
    (L : (Fin t → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2))
    (b : List (Pivot n t)) (r : Row n t)
    (hb : ∀ p ∈ b, Represents L p.2) (hr : Represents L r) :
    ∀ p ∈ typedInsert b r, Represents L p.2 := by
  unfold typedInsert
  dsimp only
  split
  · intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · exact hb p hp
    · obtain rfl := List.mem_singleton.mp hp
      exact represents_typedReduce L b r hr hb
  · exact hb
end
end MIPRE.LowDegree.BinaryLinear

namespace MIPRE.LowDegree.BinaryLinear
section
open Cost Cost.PolyTimeFun
variable {n t : ℕ}
theorem represents_fold_typedInsert
    (L : (Fin t → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2))
    (rows : List (Row n t)) (b : List (Pivot n t))
    (hb : ∀ p ∈ b, Represents L p.2) (hr : ∀ r ∈ rows, Represents L r) :
    ∀ p ∈ rows.foldl typedInsert b, Represents L p.2 := by
  induction rows generalizing b with
  | nil => exact hb
  | cons r rows ih =>
    exact ih _ (represents_typedInsert L b r hb (hr r (by simp)))
      (fun s hs => hr s (by simp [hs]))
end
end MIPRE.LowDegree.BinaryLinear

namespace MIPRE.LowDegree.BinaryLinear
section
open Cost Cost.PolyTimeFun
variable {n t : ℕ}
/-- Every constructed basis row retains its expression in the original generating family. -/
theorem typedBasis_represents
    (L : (Fin t → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2))
    (rows : List (Row n t)) (hr : ∀ r ∈ rows, Represents L r) :
    ∀ p ∈ typedBasis rows, Represents L p.2 :=
  represents_fold_typedInsert L rows [] (by simp) hr
end
end MIPRE.LowDegree.BinaryLinear

namespace MIPRE.LowDegree.BinaryLinear
section
open Cost Cost.PolyTimeFun
variable {n t : ℕ}
theorem typedReduce_error
    (L : (Fin t → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2))
    (b : List (Pivot n t)) (r : Row n t) (hb : ∀ p ∈ b, Represents L p.2) :
    (typedReduce b r).1 + L (typedReduce b r).2 = r.1 + L r.2 := by
  induction b generalizing r with
  | nil => rfl
  | cons p b ih =>
    change (typedReduce b (typedReduceStep r p)).1 + L (typedReduce b (typedReduceStep r p)).2 = _
    rw [ih _ (fun q hq => hb q (by simp [hq])), typedReduceStep_error L r p (hb p (by simp))]
end
end MIPRE.LowDegree.BinaryLinear

namespace MIPRE.LowDegree.BinaryLinear
section
open Cost Cost.PolyTimeFun
variable {n t : ℕ}
/-- Reducing a target with an initially zero certificate solves the original system. -/
theorem solve_certificate
    (L : (Fin t → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2))
    (b : List (Pivot n t)) (hb : IsPivotBasis b) (hrep : ∀ p ∈ b, Represents L p.2)
    (v : Fin n → ZMod 2) (hv : v ∈ pivotSpan b) :
    L (typedReduce b (v, 0)).2 = v := by
  have h := typedReduce_error L b (v, 0) hrep
  rw [hb.reduce_eq_zero (v, 0) hv, zero_add, map_zero, add_zero] at h
  exact h
end
end MIPRE.LowDegree.BinaryLinear

namespace MIPRE.LowDegree.BinaryLinear
section
open Cost Cost.PolyTimeFun
variable {n t : ℕ}
/-- Correctness of the actual uniform binary solver on every target in the basis span. -/
theorem solveBitsProg_correct
    (L : (Fin t → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2))
    (b : List (Pivot n t)) (hb : IsPivotBasis b) (hrep : ∀ p ∈ b, Represents L p.2)
    (v : Fin n → ZMod 2) (hv : v ∈ pivotSpan b) :
    L (vectorValue t (solveBitsProg (unary t, b.map pivotBits, vectorBits v))) = v := by
  have hz : List.replicate t false = vectorBits (0 : Fin t → ZMod 2) := by
    simp [vectorBits, bit]
  change L (vectorValue t (reduceRows (b.map pivotBits)
    (vectorBits v, List.replicate (unary t).length false)).2) = v
  rw [length_unary, hz]
  change L (vectorValue t (reduceRows (b.map pivotBits) (rowBits (v, 0))).2) = v
  rw [reduceRows_rowBits]
  change L (vectorValue t (vectorBits (typedReduce b (v, 0)).2)) = v
  rw [vectorValue_vectorBits]
  exact solve_certificate L b hb hrep v hv
end
end MIPRE.LowDegree.BinaryLinear

namespace MIPRE.LowDegree.BinaryLinear
section
open Cost Cost.PolyTimeFun
variable {n t : ℕ}
/-- The program solves any consistent binary linear system with supplied generator coordinates. -/
theorem basisSolveProg_correct
    (L : (Fin t → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2))
    (rows : List (Row n t)) (hr : ∀ r ∈ rows, Represents L r)
    (v : Fin n → ZMod 2) (hv : v ∈ rowSpan rows) :
    L (vectorValue t (basisSolveProg (unary t, rows.map rowBits, vectorBits v))) = v := by
  change L (vectorValue t (solveBitsProg (unary t, basisRowsProg (rows.map rowBits), vectorBits v))) = v
  rw [basisRowsProg_correct]
  apply solveBitsProg_correct L _ (typedBasis_isPivotBasis rows) (typedBasis_represents L rows hr) v
  rwa [typedBasis_span]
end
end MIPRE.LowDegree.BinaryLinear

namespace MIPRE.LowDegree.BinaryLinear
section
open Cost Cost.PolyTimeFun
theorem columnRows_represents {m n : ℕ} (A : Matrix (Fin m) (Fin n) (ZMod 2)) :
    ∀ r ∈ columnRows A, Represents A.mulVecLin r := by
  intro r hr
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hr
  exact Matrix.mulVec_single_one A j
end
end MIPRE.LowDegree.BinaryLinear

namespace MIPRE.LowDegree.BinaryLinear
section
open Cost Cost.PolyTimeFun
theorem rowSpan_columnRows {m n : ℕ} (A : Matrix (Fin m) (Fin n) (ZMod 2)) :
    rowSpan (columnRows A) = A.mulVecLin.range := by
  rw [Matrix.range_mulVecLin]
  unfold rowSpan
  congr 1
  ext v
  simp only [Set.mem_setOf_eq, columnRows, List.mem_ofFn, Set.mem_range]
  constructor
  · rintro ⟨r, ⟨j, rfl⟩, hr⟩
    exact ⟨j, hr⟩
  · rintro ⟨j, hj⟩
    exact ⟨(A.col j, Pi.single j 1), ⟨j, rfl⟩, hj⟩
end
end MIPRE.LowDegree.BinaryLinear

namespace MIPRE.LowDegree.BinaryLinear
section
open Cost Cost.PolyTimeFun
/-- A globally polynomial-time solver for every consistent binary matrix system. -/
theorem matrixSolveProg_correct {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) (ZMod 2)) (v : Fin m → ZMod 2)
    (hv : ∃ x, A.mulVec x = v) :
    A.mulVec (vectorValue n (matrixSolveProg (unary n, matrixBits A, vectorBits v))) = v := by
  change A.mulVecLin (vectorValue n (basisSolveProg
    (unary n, coordinateRows (transposeBits (unary n).length (matrixBits A)), vectorBits v))) = v
  rw [length_unary, coordinateRows_matrixBits]
  apply basisSolveProg_correct A.mulVecLin _ (columnRows_represents A) v
  rw [rowSpan_columnRows, LinearMap.mem_range]
  exact hv
end
end MIPRE.LowDegree.BinaryLinear

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

namespace MIPRE.Introspection.CLChecks
noncomputable section
open Finset Classical
set_option linter.unusedSectionVars false
variable {F ι : Type*} [Field F] [Fintype ι] [DecidableEq ι] {ℓ : ℕ}
/-- Adding the selected next linear answer advances the actual sampler prefix. -/
theorem truncate_eval_step {P : CL.CLFun F ι ℓ} {T : Finset ι}
    (hP : P.SupportedOn T) (k : ℕ) (x : ι → F) :
    (P.truncate (k + 1)).eval x = (P.truncate k).eval x +
      (stageLinear P k ((P.truncate k).eval x)) x := by
  rw [hP.eval_truncate_eq_sum (k + 1), sum_range_succ,
    ← hP.eval_truncate_eq_sum k]
  congr 1
  rw [← CL.RegLinear.toLinearMap_apply, stageLinear_toLinearMap, hP.mapOfPrefix_eval]
end
end MIPRE.Introspection.CLChecks

namespace MIPRE.Introspection.AuxiliaryPrefix
noncomputable section
open Finset CLChecks
variable {F ι : Type*} [Field F] [Fintype ι] [DecidableEq ι] {ℓ : ℕ}
theorem outputPrefix_step {P : CL.CLFun F ι ℓ} {T : Finset ι}
    (hP : P.SupportedOn T) (k : ℕ) (y : ι → F) :
    P.outputPrefix (k + 1) y = P.outputPrefix k y + CL.proj (P.factorOfPrefix k y) y := by
  have hd : Disjoint (prefixRegister P k y) (P.factorOfPrefix k y) := by
    apply disjoint_left.mpr
    intro i hi hs
    exact (mem_sdiff.mp (stageFactor_subset_residual hP k y hs)).2 hi
  rw [← proj_prefixRegister hP, prefixRegister_step, CL.proj_union_of_disjoint hd,
    proj_prefixRegister hP]
end
end MIPRE.Introspection.AuxiliaryPrefix

namespace MIPRE.Introspection.AuxiliaryPrefix
noncomputable section
open Finset CLChecks
open LowDegree.BinaryLinear Cost
variable {F ι : Type*} [Field F] [Fintype ι] [DecidableEq ι] {ℓ : ℕ}
theorem solveStage_correct {n : ℕ}
    (L : (Fin n → CL.𝔽₂) →ₗ[CL.𝔽₂] (Fin n → CL.𝔽₂))
    (v : Fin n → CL.𝔽₂) (hv : ∃ x, L x = v) : L (solveStage L v) = v := by
  have he : (LinearMap.toMatrix' L).mulVecLin = L := Matrix.toLin'_toMatrix' L
  have hv' : ∃ x, (LinearMap.toMatrix' L).mulVec x = v := by
    simpa only [← Matrix.mulVecLin_apply, he] using hv
  have h := matrixSolveProg_correct (LinearMap.toMatrix' L) v hv'
  simpa only [← Matrix.mulVecLin_apply, he, solveStage] using h
end
end MIPRE.Introspection.AuxiliaryPrefix

namespace MIPRE.Introspection.AuxiliaryScan
noncomputable section
open Cost Cost.PolyTimeFun
theorem advance_apply (f : PolyTimeFun AuxiliarySource.Context BitStr)
    (m : PolyTimeFun AuxiliarySource.Context (List BitStr)) (k : ℕ)
    (ctx : AuxiliarySource.Context) (y : BitStr) (b : Bool) (u x : BitStr) :
    advance f m k ((ctx, y), b, u, x) =
      if b then stage f m (contextAt ctx (k + 1) u, y, x) else (false, [], []) := by
  cases b <;> rfl
end
end MIPRE.Introspection.AuxiliaryScan

namespace MIPRE.Introspection.AuxiliaryScan
noncomputable section
open Cost Cost.PolyTimeFun
theorem program_succ (f : PolyTimeFun AuxiliarySource.Context BitStr)
    (m : PolyTimeFun AuxiliarySource.Context (List BitStr)) (k : ℕ)
    (ctx : AuxiliarySource.Context) (y : BitStr) :
    program f m (k + 1) (ctx, y) = advance f m k ((ctx, y), program f m k (ctx, y)) := rfl
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
open Cost LowDegree.BinaryLinear CLChecks
variable {n ℓ : ℕ}
theorem stage_of_attained_next {P : CL.CLFun CL.𝔽₂ (Fin n) ℓ} {T : Finset (Fin n)}
    (hP : P.SupportedOn T) (k : ℕ) (y x : Fin n → CL.𝔽₂)
    (hx : (P.truncate (k + 1)).eval x = P.outputPrefix (k + 1) y) :
    P.mapOfPrefix k (P.outputPrefix k y) x = CL.proj (P.factorOfPrefix k y) y := by
  have hp := earlier_attained hP (Nat.le_succ k) y x hx
  have hs := truncate_eval_step hP k x
  rw [hx, hp, ← CL.RegLinear.toLinearMap_apply, stageLinear_toLinearMap,
    AuxiliaryPrefix.outputPrefix_step hP] at hs
  exact (add_left_cancel hs).symm
end
end MIPRE.Introspection.AuxiliaryScan

namespace MIPRE.Introspection.AuxiliaryScan
noncomputable section
open Cost LowDegree.BinaryLinear CLChecks
variable {n ℓ : ℕ}
theorem stage_at_claimed (f : PolyTimeFun AuxiliarySource.Context BitStr)
    (m : PolyTimeFun AuxiliarySource.Context (List BitStr)) (ctx : AuxiliarySource.Context)
    {P : CL.CLFun CL.𝔽₂ (Fin n) ℓ} {T : Finset (Fin n)} (hP : P.SupportedOn T)
    (k : ℕ) (y x : Fin n → CL.𝔽₂) (hx : (P.truncate k).eval x = P.outputPrefix k y)
    (hq : QueriesCorrectAt f m ctx P k) :
    stage f m (contextAt ctx (k + 1) (CL.toBits (P.outputPrefix k y)), CL.toBits y, CL.toBits x) =
      let v := CL.proj (P.factorOfPrefix k y) y
      let L := P.mapOfPrefix k (P.outputPrefix k y)
      let z := AuxiliaryPrefix.solveStage L v
      (decide (L z = v), CL.toBits (P.outputPrefix (k + 1) y),
        CL.toBits (AuxiliaryPrefix.replaceSeed P k (P.outputPrefix k y) x z)) := by
  obtain ⟨hf, hm⟩ := hq _ ⟨x, hx⟩
  rw [factorOfPrefix_outputPrefix hP] at hf
  rw [stage_correct f m _ _ _ _ _ _ rfl hf hm]
  dsimp only
  rw [AuxiliaryPrefix.outputPrefix_step hP, AuxiliaryPrefix.replaceSeed,
    factorOfPrefix_outputPrefix hP]
end
end MIPRE.Introspection.AuxiliaryScan

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Introspection.AuxiliaryScan
open Cost LowDegree.BinaryLinear CLChecks
variable {n ℓ : ℕ}
theorem _root_.solution (f : PolyTimeFun AuxiliarySource.Context BitStr)
    (m : PolyTimeFun AuxiliarySource.Context (List BitStr)) (ctx : AuxiliarySource.Context)
    {P : CL.CLFun CL.𝔽₂ (Fin n) ℓ} {T : Finset (Fin n)} (hP : P.SupportedOn T)
    (y : Fin n → CL.𝔽₂) (k : ℕ) (hq : ∀ j < k, QueriesCorrectAt f m ctx P j)
    (ha : ∃ x, (P.truncate k).eval x = P.outputPrefix k y) :
    (program f m k (ctx, CL.toBits y)).1 = true := by
  induction k with
  | zero => rfl
  | succ k ih =>
    obtain ⟨x, hx⟩ := ha
    have hp := ih (fun j hj => hq j (by omega))
      ⟨x, earlier_attained hP (Nat.le_succ k) y x hx⟩
    obtain ⟨z, he, hz⟩ := program_sound f m ctx hP y k
      (fun j hj => hq j (by omega)) hp
    have hs := stage_at_claimed f m ctx hP k y z hz (hq k (by omega))
    rw [program_succ, he, advance_apply]
    simp only [if_true]
    rw [hs]
    dsimp only
    apply decide_eq_true
    exact AuxiliaryPrefix.solveStage_correct _ _ ⟨x, stage_of_attained_next hP k y x hx⟩
end MIPRE.Introspection.AuxiliaryScan
