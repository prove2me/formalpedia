-- Prove2me | solution 1 for MIPRE.Introspection.AuxiliaryScan.stage_correct
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T04:48:35.734209+00:00
-- url     : https://prove2.me/submissions/9f0e8a3e-aff0-4004-b3b0-10fbad27d272

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/AuxiliaryScanStage.lean (solution of MIPRE.Introspection.AuxiliaryScan.stage_correct);
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
import Theorems.Thm_MIPRE_Cost_encode_injective
import Theorems.Thm_MIPRE_LowDegree_BinaryLinear_basisSolveProg_encoding
import Theorems.Thm_MIPRE_LowDegree_BinaryLinear_coordinateRows_matrixBits
import Theorems.Thm_MIPRE_LowDegree_BinaryLinear_xorBits_vectorBits

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.LowDegree.BinaryLinear
section
open Cost Cost.PolyTimeFun
theorem ofBool_injective : Function.Injective (ofBool : Bool → ZMod 2) := by
  intro a b h
  have := congrArg bit h
  simpa using this
end
end MIPRE.LowDegree.BinaryLinear

namespace MIPRE.LowDegree.BinaryLinear
section
open Cost Cost.PolyTimeFun
theorem ofBool_xor (a b : Bool) :
    (ofBool (a ^^ b) : ZMod 2) = ofBool a + ofBool b := by
  cases a <;> cases b <;> decide
end
end MIPRE.LowDegree.BinaryLinear

namespace MIPRE.LowDegree.BinaryLinear
section
open Cost Cost.PolyTimeFun
theorem ofBool_and (a b : Bool) :
    (ofBool (a && b) : ZMod 2) = ofBool a * ofBool b := by
  cases a <;> cases b <;> decide
end
end MIPRE.LowDegree.BinaryLinear

namespace MIPRE.LowDegree.BinaryLinear
section
open Cost Cost.PolyTimeFun
theorem ofBool_fold_dotStep (l : List (Bool × Bool)) (b : Bool) :
    (ofBool (l.foldl dotStep b) : ZMod 2) =
      ofBool b + (l.map (fun p => (ofBool p.1 : ZMod 2) * ofBool p.2)).sum := by
  induction l generalizing b with
  | nil => simp
  | cons p l ih =>
    rw [List.foldl_cons, ih]
    simp only [dotStep, ofBool_xor, ofBool_and, List.map_cons, List.sum_cons]
    ring
end
end MIPRE.LowDegree.BinaryLinear

namespace MIPRE.LowDegree.BinaryLinear
section
open Cost Cost.PolyTimeFun
theorem ofBool_dotBits (a b : BitStr) :
    (ofBool (dotBits a b) : ZMod 2) =
      ((a.zip b).map (fun p => (ofBool p.1 : ZMod 2) * ofBool p.2)).sum := by
  rw [dotBits, ofBool_fold_dotStep]
  simp [ofBool]
end
end MIPRE.LowDegree.BinaryLinear

namespace MIPRE.LowDegree.BinaryLinear
section
open Cost Cost.PolyTimeFun
theorem zip_vectorBits {n : ℕ} (v w : Fin n → ZMod 2) :
    (vectorBits v).zip (vectorBits w) = List.ofFn (fun i => (bit (v i), bit (w i))) := by
  apply List.ext_getElem
  · simp [vectorBits]
  · intro i hi hj
    simp [vectorBits]
end
end MIPRE.LowDegree.BinaryLinear

namespace MIPRE.LowDegree.BinaryLinear
section
open Cost Cost.PolyTimeFun
/-- The raw parity circuit computes the exact binary dot product. -/
theorem dotBits_vectorBits {n : ℕ} (v w : Fin n → ZMod 2) :
    dotBits (vectorBits v) (vectorBits w) = bit (∑ i, v i * w i) := by
  apply ofBool_injective
  rw [ofBool_dotBits, zip_vectorBits, ofBool_bit]
  simp only [List.map_ofFn, List.sum_ofFn, Function.comp_apply, ofBool_bit]
end
end MIPRE.LowDegree.BinaryLinear

namespace MIPRE.LowDegree.BinaryLinear
section
open Cost Cost.PolyTimeFun
/-- Executable matrix application agrees with the usual binary matrix-vector product. -/
theorem applyBits_matrixBits {m n : ℕ} (A : Matrix (Fin m) (Fin n) (ZMod 2))
    (v : Fin n → ZMod 2) :
    applyBits (matrixBits A) (vectorBits v) = vectorBits (A.mulVec v) := by
  simp only [applyBits, matrixBits, List.map_ofFn, vectorBits]
  apply congrArg List.ofFn
  funext i
  exact dotBits_vectorBits (A i) v
end
end MIPRE.LowDegree.BinaryLinear

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

namespace MIPRE.Introspection.AuxiliaryBits
noncomputable section
open Cost Cost.PolyTimeFun LowDegree.BinaryLinear LowDegree.BinaryPolynomial
theorem replace_correct {n : ℕ} (S : Finset (Fin n)) (x z : Fin n → CL.𝔽₂) :
    replace (CL.indicatorBits S, CL.toBits x, CL.toBits z) =
      CL.toBits (CL.proj Sᶜ x + CL.proj S z) := by
  change xorBits (mask (complement (CL.indicatorBits S), CL.toBits x))
    (mask (CL.indicatorBits S, CL.toBits z)) = _
  rw [complement_correct, mask_correct, mask_correct]
  exact xorBits_vectorBits _ _
end
end MIPRE.Introspection.AuxiliaryBits

namespace MIPRE.Introspection.AuxiliaryBits
noncomputable section
open Cost Cost.PolyTimeFun LowDegree.BinaryLinear LowDegree.BinaryPolynomial
theorem matrixSolve_encoding {m n : ℕ} (A : Matrix (Fin m) (Fin n) CL.𝔽₂)
    (v : Fin m → CL.𝔽₂) :
    matrixSolveProg (unary n, matrixBits A, CL.toBits v) =
      CL.toBits (vectorValue n (matrixSolveProg (unary n, matrixBits A, CL.toBits v))) := by
  have he : matrixSolveProg (unary n, matrixBits A, CL.toBits v) =
      vectorBits (typedReduce (typedBasis (columnRows A)) (v, 0)).2 := by
    change basisSolveProg (unary n,
      coordinateRows (transposeBits (unary n).length (matrixBits A)), vectorBits v) = _
    rw [length_unary, coordinateRows_matrixBits, basisSolveProg_encoding]
  rw [he]
  change vectorBits _ = vectorBits (vectorValue n (vectorBits _))
  rw [vectorValue_vectorBits]
end
end MIPRE.Introspection.AuxiliaryBits

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Introspection.AuxiliaryScan
open Cost Cost.PolyTimeFun CL.Detyping.Program LowDegree.BinaryLinear LowDegree.BinaryPolynomial
set_option backward.isDefEq.respectTransparency false in
theorem _root_.solution (f : PolyTimeFun AuxiliarySource.Context BitStr) (m : PolyTimeFun AuxiliarySource.Context (List BitStr)) (ctx : AuxiliarySource.Context) {n : ℕ}
    (S : Finset (Fin n)) (L : (Fin n → CL.𝔽₂) →ₗ[CL.𝔽₂] (Fin n → CL.𝔽₂))
    (u y x : Fin n → CL.𝔽₂)
    (hu : AuxiliarySource.inputPrefix ctx = CL.toBits u)
    (hS : f ctx = CL.indicatorBits S)
    (hL : m ctx = matrixBits (LinearMap.toMatrix' L)) :
    stage f m (ctx, CL.toBits y, CL.toBits x) =
      let v := CL.proj S y
      let z := AuxiliaryPrefix.solveStage L v
      (decide (L z = v), CL.toBits (u + v), CL.toBits (CL.proj Sᶜ x + CL.proj S z)) := by
  have ht : target f (ctx, CL.toBits y, CL.toBits x) = CL.toBits (CL.proj S y) := by
    change AuxiliaryBits.mask (f ctx, CL.toBits y) = _
    rw [hS, AuxiliaryBits.mask_correct]
  have hz : MIPRE.Introspection.AuxiliaryScan.solution f m (ctx, CL.toBits y, CL.toBits x) =
      CL.toBits (AuxiliaryPrefix.solveStage L (CL.proj S y)) := by
    change matrixSolveProg (unary (CL.toBits y).length,
      m ctx, target f (ctx, CL.toBits y, CL.toBits x)) = _
    rw [CL.length_toBits, hL, ht, AuxiliaryBits.matrixSolve_encoding]
    rfl
  have hm : applyBits (matrixBits (LinearMap.toMatrix' L))
      (CL.toBits (AuxiliaryPrefix.solveStage L (CL.proj S y))) =
        CL.toBits (L (AuxiliaryPrefix.solveStage L (CL.proj S y))) := by
    change applyBits (matrixBits (LinearMap.toMatrix' L))
      (vectorBits (AuxiliaryPrefix.solveStage L (CL.proj S y))) =
      vectorBits (L (AuxiliaryPrefix.solveStage L (CL.proj S y)))
    rw [applyBits_matrixBits]
    congr 1
    exact congrArg (fun f => f (AuxiliaryPrefix.solveStage L (CL.proj S y)))
      (Matrix.toLin'_toMatrix' L)
  simp only [stage, pair_apply, AuxiliaryProgram.equal, ap₂_apply, comp_apply,
    encoded_apply, treeEq_apply]
  change (decide (encode (applyBits (m ctx)
    (MIPRE.Introspection.AuxiliaryScan.solution f m (ctx, CL.toBits y, CL.toBits x))) =
      encode (target f (ctx, CL.toBits y, CL.toBits x))),
    xorBits (AuxiliarySource.inputPrefix ctx) (target f (ctx, CL.toBits y, CL.toBits x)),
    AuxiliaryBits.replace (f ctx, CL.toBits x,
      MIPRE.Introspection.AuxiliaryScan.solution f m (ctx, CL.toBits y, CL.toBits x))) = _
  have hadd : xorBits (CL.toBits u) (CL.toBits (CL.proj S y)) =
      CL.toBits (u + CL.proj S y) := xorBits_vectorBits _ _
  rw [hL, hS, hu, hz, ht, hm, AuxiliaryBits.replace_correct, hadd]
  simp only [encode_injective.eq_iff, AuxiliaryProgram.toBits_injective.eq_iff]
end MIPRE.Introspection.AuxiliaryScan
