-- Prove2me | solution 1 for MIPRE.Introspection.ClockedSourceChecks.sampling_eq_program
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T05:03:17.873663+00:00
-- url     : https://prove2.me/submissions/9664277c-d650-4894-8756-eafc310f02fa

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/ClockedSourceChecks.lean (solution of MIPRE.Introspection.ClockedSourceChecks.sampling_eq_program);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Degree
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
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Kronecker
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
import Definitions.Def_MIPRE_Foundations_Cost_Binary
import Definitions.Def_MIPRE_Foundations_SAT_Formula
import Definitions.Def_MIPRE_Foundations_SAT_FmlLib
import Definitions.Def_MIPRE_Foundations_SAT_Flatten
import Definitions.Def_MIPRE_Foundations_Cost_Reader
import Definitions.Def_MIPRE_Foundations_SAT_FmlProg
import Definitions.Def_MIPRE_Foundations_SAT_ArrayProg
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
import Definitions.Def_MIPRE_Foundations_Introspection_SourceCompilerParams
import Definitions.Def_MIPRE_Foundations_Introspection_Clock
import Definitions.Def_MIPRE_Foundations_Introspection_ClockCost
import Definitions.Def_MIPRE_Foundations_Introspection_ClockSimulation
import Definitions.Def_MIPRE_Foundations_Introspection_ClockCompiler
import Definitions.Def_MIPRE_Foundations_Introspection_ClockSimulationCost
import Definitions.Def_MIPRE_Foundations_Introspection_SourceCompilerParamsCost
import Definitions.Def_MIPRE_Foundations_Introspection_SourceCompilerGuard
import Definitions.Def_MIPRE_Foundations_Introspection_ParserGuard
import Definitions.Def_MIPRE_Foundations_Introspection_SourceCompiler
import Definitions.Def_MIPRE_Foundations_Introspection_SourceCompilerCost
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
import Definitions.Def_MIPRE_Foundations_Introspection_AuxiliarySamplingProgram
import Definitions.Def_MIPRE_Foundations_Introspection_Readout
import Definitions.Def_MIPRE_Foundations_Introspection_FinalExtraction
import Definitions.Def_MIPRE_Foundations_Introspection_TypeGraph
import Definitions.Def_MIPRE_Foundations_Introspection_HonestCore
import Definitions.Def_MIPRE_Foundations_Introspection_SourcePadding
import Definitions.Def_MIPRE_Foundations_Introspection_AuxiliaryRegisterBits
import Definitions.Def_MIPRE_Foundations_Introspection_AuxiliarySamplingCorrect
import Definitions.Def_MIPRE_Foundations_Introspection_ClockedSourceChecks
import Theorems.Thm_MIPRE_CL_Detyping_Program_readNat_encode
import Theorems.Thm_MIPRE_Cost_encode_injective
import Theorems.Thm_MIPRE_Introspection_AuxiliaryProgram_equal_iff
import Theorems.Thm_MIPRE_Introspection_AuxiliaryProgram_samplingProg_accepts_iff

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.Introspection.ClockSimulation
noncomputable section
open Cost Cost.Prog Cost.PolyTimeFun CL.Detyping CL.Detyping.Program
theorem reindexed_cons (n : ℕ) (d : Data) :
    reindexed (.cons (encode n) d) = .cons (encode (2 ^ n)) d := by
  simp only [reindexed, indexReader, comp_apply, treeHead_cons, treeTail_cons, readNat_encode]
end
end MIPRE.Introspection.ClockSimulation

namespace MIPRE.Introspection.SourceCompiler
noncomputable section
open Cost Cost.Prog Cost.PolyTimeFun CL.Detyping.Program
open CL.Detyping.DeciderProgram (lengthNat lengthNat_apply)
theorem sourceCheck_iff (y : BitStr) (s : ℕ) : sourceCheck (y,s) = true ↔ InSource s y := by
  simp only [sourceCheck, ap₂_apply, comp_apply, encoded_apply, treeEq_apply,
    DynamicParser.dropBits_apply, decide_eq_true_eq, encode_injective.eq_iff]
  change y.drop s = (y.drop s).map (fun _ => false) ↔ InSource s y
  simp only [List.map_const', List.length_drop, InSource]
end
end MIPRE.Introspection.SourceCompiler

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
open Cost Cost.Prog Cost.PolyTimeFun CL.Detyping.Program
open SourceCompiler (GuardInput inputIndex inputQ inputR inputDim inputLeft inputRight leftParts rightParts readInput)
theorem samplingReady_iff (x : SamplingInput) : samplingReady x = true ↔ SamplingReady x := by
  simp only [samplingReady,andCheck_iff,ap₂_apply,const_apply,leNat_apply,decide_eq_true_eq,
    comp_apply,samplingLevel,samplingFields,fst_apply,snd_apply,SourceCompiler.sourceCheck_iff,
    pair_apply,equal_iff,SamplingReady]
end
end MIPRE.Introspection.AuxiliaryProgram

namespace MIPRE.Introspection.AuxiliaryProgram
noncomputable section
open Cost Cost.Prog Cost.PolyTimeFun CL.Detyping.Program
open SourceCompiler (GuardInput inputIndex inputQ inputR inputDim inputLeft inputRight leftParts rightParts readInput)
theorem samplingCall_apply (x : SamplingInput) : samplingCall x =
    encode (inputIndex x.2.2, CL.Sampler.Query.marginal (Player.ofBool x.2.1) x.1
      ((rightParts x.2.2).1.take (inputDim x.2.2))) := by
  cases hw : x.2.1 <;>
    simp [samplingCall,samplingFields,samplingRole,samplingLevel,DynamicParser.takeBits_apply,
      Player.ofBool,hw,encode_prod]
  <;> rfl
end
end MIPRE.Introspection.AuxiliaryProgram

namespace MIPRE.Introspection.ClockedSourceChecks
noncomputable section
open Cost Cost.PolyTimeFun CL.Detyping.Program AuxiliaryProgram SourceCompiler
theorem sampling_iff (U : ClockedUniversalMachine) (b : Unary) (S : Prog)
    (x : SamplingInput) :
    sampling U (b, S, x) = true ↔ SamplingReady x ∧
      clockedResult S (samplingCall x) b.length = samplingExpected x := by
  simp only [sampling, MIPRE.Introspection.AuxiliaryProgram.andCheck_iff, equal_iff, comp_apply, pair_apply,
    fst_apply, snd_apply, ClockedQuery.run_apply, samplingReady_iff]
end
end MIPRE.Introspection.ClockedSourceChecks

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Introspection.ClockedSourceChecks
open Cost Cost.PolyTimeFun CL.Detyping.Program AuxiliaryProgram SourceCompiler
theorem _root_.solution (U : ClockedUniversalMachine) (k lam n j Q R s : ℕ)
    (S : Prog) (w : Bool) (a b : BitStr) :
    sampling U (unary (ansBound k lam n), S, j, w, 2 ^ n, Q, R, s, a, b) = true ↔
      ∃ t, (samplingProg k lam U S).Runs (encode (j,w,n,Q,R,s,a,b)) (encode true) t := by
  rw [sampling_iff, samplingProg_accepts_iff]
  simp only [SamplingRawReady, readSamplingInput_encode, true_and, length_unary]
  have hr : SamplingReady (j,w,2 ^ n,Q,R,s,a,b) = SamplingReady (j,w,n,Q,R,s,a,b) := rfl
  rw [hr]
  apply and_congr_right
  intro _
  rw [samplingResult, samplingCall_apply, samplingCall_apply]
  have hi : ClockSimulation.indexReader
      (encode (n,CL.Sampler.Query.marginal (Player.ofBool w) j
        ((rightParts (n,Q,R,s,a,b)).1.take s))) = n := readNat_encode n
  change clockedResult S (encode (2 ^ n,CL.Sampler.Query.marginal (Player.ofBool w) j
      ((rightParts (n,Q,R,s,a,b)).1.take s))) (ansBound k lam n) = _ ↔ _
  simp only [inputIndex, inputDim, comp_apply, fst_apply, snd_apply]
  have he : ClockSimulation.reindexed (encode (n,CL.Sampler.Query.marginal (Player.ofBool w) j
      ((rightParts (n,Q,R,s,a,b)).1.take s))) = encode (2 ^ n,
      CL.Sampler.Query.marginal (Player.ofBool w) j ((rightParts (n,Q,R,s,a,b)).1.take s)) :=
    ClockSimulation.reindexed_cons n _
  rw [hi, he]
  rfl
end MIPRE.Introspection.ClockedSourceChecks
