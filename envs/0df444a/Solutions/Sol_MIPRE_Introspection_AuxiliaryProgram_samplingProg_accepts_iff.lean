-- Prove2me | solution 1 for MIPRE.Introspection.AuxiliaryProgram.samplingProg_accepts_iff
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T04:58:12.821899+00:00
-- url     : https://prove2.me/submissions/3db4fe38-c04c-44c8-a1c7-75e477a760c4

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/AuxiliarySamplingProgram.lean (solution of MIPRE.Introspection.AuxiliaryProgram.samplingProg_accepts_iff);
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
import Definitions.Def_MIPRE_Foundations_Introspection_AuxiliarySamplingProgram
import Theorems.Thm_MIPRE_Cost_Eval_deterministic
import Theorems.Thm_MIPRE_Cost_Prog_routeOneCall_closed
import Theorems.Thm_MIPRE_Cost_Prog_routeOneCall_direct
import Theorems.Thm_MIPRE_Cost_Prog_routeOneCall_indirect
import Theorems.Thm_MIPRE_Cost_encode_injective
import Theorems.Thm_MIPRE_Introspection_AuxiliaryProgram_equal_iff

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

namespace MIPRE.Introspection.ClockSimulation
noncomputable section
open Cost Cost.Prog Cost.PolyTimeFun CL.Detyping CL.Detyping.Program
theorem reindexProg_closed : reindexProg.WellScoped 1 :=
  ⟨indexReader.closed, toUnaryProg_wellScoped.mono (by omega) _,
    expBitsProg_wellScoped.mono (by omega) _, by simp [WellScoped],
    callVar_wellScoped (by omega) treeTail.closed⟩
end
end MIPRE.Introspection.ClockSimulation

namespace MIPRE.Introspection.ClockSimulation
noncomputable section
open Cost Cost.Prog Cost.PolyTimeFun CL.Detyping CL.Detyping.Program
/-- The source-index adapter is total even when the incoming index is malformed. -/
theorem reindexProg_runs (x : Data) : ∃ time, reindexProg.Runs x (reindexed x) time := by
  obtain ⟨ti, _, hi⟩ := indexReader.computes x
  obtain ⟨tu, _, hu⟩ := toUnaryProg_runs (indexReader x)
  obtain ⟨te, _, he⟩ := expBitsProg_runs (indexReader x)
  obtain ⟨td, _, hd⟩ := treeTail.computes x
  exact ⟨_, Eval.let_ hi (Eval.let_ (Eval.append_of_wellScoped hu toUnaryProg_wellScoped _)
    (Eval.let_ (Eval.append_of_wellScoped he expBitsProg_wellScoped _)
      (Eval.cons (Eval.var_of_get (i := 0) (by simp))
        (callVar_eval (i := 3) treeTail.closed (by simp) hd))))⟩
end
end MIPRE.Introspection.ClockSimulation

namespace MIPRE.Introspection.ClockSimulation
noncomputable section
open Cost Cost.Prog Cost.PolyTimeFun CL.Detyping CL.Detyping.Program
theorem clockStage_closed (k lam : ℕ) : (clockStage k lam).WellScoped 1 :=
  Prog.routeOneCall_closed _ (growingClock k lam).closed _
end
end MIPRE.Introspection.ClockSimulation

namespace MIPRE.Introspection.ClockSimulation
noncomputable section
open Cost Cost.Prog Cost.PolyTimeFun CL.Detyping CL.Detyping.Program
theorem clockStage_runs (k lam : ℕ) (x : Data) :
    ∃ time, (clockStage k lam).Runs x (.cons x (.ofNat (ansBound k lam (indexReader x)))) time := by
  obtain ⟨time, hr⟩ := (growingClock k lam).runs (indexReader x)
  exact Prog.routeOneCall_indirect ClockProgram.clockRoute (growingClock k lam).closed
    treePair x _ x _ time rfl hr
end
end MIPRE.Introspection.ClockSimulation

namespace MIPRE.Introspection.ClockSimulation
noncomputable section
open Cost Cost.Prog Cost.PolyTimeFun CL.Detyping CL.Detyping.Program
theorem reindexStage_closed (source : Prog) : (reindexStage source).WellScoped 1 :=
  callWithContext_closed reindexProg_closed _
end
end MIPRE.Introspection.ClockSimulation

namespace MIPRE.Introspection.ClockSimulation
noncomputable section
open Cost Cost.Prog Cost.PolyTimeFun CL.Detyping CL.Detyping.Program
theorem reindexStage_runs (source : Prog) (x : Data) (budget : ℕ) :
    ∃ time, (reindexStage source).Runs (.cons x (.ofNat budget))
      (.cons (.ofNat budget) (.cons (encode source) (reindexed x))) time := by
  obtain ⟨time, hr⟩ := reindexProg_runs x
  exact callWithContext_runs reindexProg_closed (simulationInput source) x (.ofNat budget)
    (reindexed x) time hr
end
end MIPRE.Introspection.ClockSimulation

namespace MIPRE.Introspection.ClockSimulation
noncomputable section
open Cost Cost.Prog Cost.PolyTimeFun CL.Detyping CL.Detyping.Program
theorem prog_closed (k lam : ℕ) (U : ClockedUniversalMachine) (source : Prog) :
    (prog k lam U source).WellScoped 1 :=
  ⟨clockStage_closed k lam, (reindexStage_closed source).mono (by omega) _,
    U.closed.mono (by omega) _⟩
end
end MIPRE.Introspection.ClockSimulation

namespace MIPRE.Introspection.ClockSimulation
noncomputable section
open Cost Cost.Prog Cost.PolyTimeFun CL.Detyping CL.Detyping.Program
theorem prog_runs (k lam : ℕ) (U : ClockedUniversalMachine) (source : Prog) (x : Data) :
    ∃ time, (prog k lam U source).Runs x
      (clockedResult source (reindexed x) (ansBound k lam (indexReader x))) time := by
  obtain ⟨tc, hc⟩ := clockStage_runs k lam x
  obtain ⟨tr, hr⟩ := reindexStage_runs source x (ansBound k lam (indexReader x))
  obtain ⟨tu, _, hu⟩ := U.run source (reindexed x) (ansBound k lam (indexReader x))
  exact ⟨_, Eval.let_ hc (Eval.append_of_wellScoped
    (Eval.let_ hr (Eval.append_of_wellScoped hu U.closed _))
      ⟨reindexStage_closed source, U.closed.mono (by omega) _⟩ _)⟩
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
theorem samplingRoute_apply (x : Data) : samplingRoute x = if SamplingRawReady x then
    (true,.cons (samplingCall (readSamplingInput x)) x) else (false,encode false) := by
  simp only [samplingRoute,PolyTimeFun.ite_apply,andCheck_iff,equal_iff,id_apply,comp_apply,
    encoded_apply,samplingReady_iff,SamplingRawReady,pair_apply,const_apply,ap₂_apply,treePair_apply]
  congr 1
end
end MIPRE.Introspection.AuxiliaryProgram

namespace MIPRE.Introspection.AuxiliaryProgram
noncomputable section
open Cost Cost.Prog Cost.PolyTimeFun CL.Detyping.Program
open SourceCompiler (GuardInput inputIndex inputQ inputR inputDim inputLeft inputRight leftParts rightParts readInput)
theorem samplingPost_apply (x r : Data) : samplingPost (x,r) =
    encode (decide (r = samplingExpected (readSamplingInput x))) := by
  simp [samplingPost,equal]
end
end MIPRE.Introspection.AuxiliaryProgram

namespace MIPRE.Introspection.AuxiliaryProgram
noncomputable section
open Cost Cost.Prog Cost.PolyTimeFun CL.Detyping.Program
open SourceCompiler (GuardInput inputIndex inputQ inputR inputDim inputLeft inputRight leftParts rightParts readInput)
set_option backward.isDefEq.respectTransparency false in
theorem samplingProg_run (k lam : ℕ) (U : ClockedUniversalMachine) (S : Prog) (x : Data) :
    ∃ t, (samplingProg k lam U S).Runs x
      (if SamplingRawReady x then encode (decide
        (samplingResult k lam S (readSamplingInput x) = samplingExpected (readSamplingInput x)))
       else encode false) t := by
  by_cases h : SamplingRawReady x
  · obtain ⟨t,hr⟩ := ClockSimulation.prog_runs k lam U S (samplingCall (readSamplingInput x))
    obtain ⟨time,ht⟩ := routeOneCall_indirect samplingRoute (ClockSimulation.prog_closed k lam U S)
      samplingPost x _ x _ t (by rw [samplingRoute_apply,if_pos h]) hr
    refine ⟨time,?_⟩
    simpa only [samplingProg,if_pos h,samplingPost_apply,samplingResult] using ht
  · obtain ⟨t,ht⟩ := routeOneCall_direct samplingRoute (ClockSimulation.prog k lam U S)
      samplingPost x (encode false) (by rw [samplingRoute_apply,if_neg h])
    exact ⟨t,by simpa only [samplingProg,if_neg h] using ht⟩
end
end MIPRE.Introspection.AuxiliaryProgram

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Introspection.AuxiliaryProgram
open Cost Cost.Prog Cost.PolyTimeFun CL.Detyping.Program
open SourceCompiler (GuardInput inputIndex inputQ inputR inputDim inputLeft inputRight leftParts rightParts readInput)
theorem _root_.solution (k lam : ℕ) (U : ClockedUniversalMachine) (S : Prog) (x : Data) :
    (∃ t, (samplingProg k lam U S).Runs x (encode true) t) ↔
      SamplingRawReady x ∧ samplingResult k lam S (readSamplingInput x) =
        samplingExpected (readSamplingInput x) := by
  obtain ⟨t,ht⟩ := samplingProg_run k lam U S x
  by_cases h : SamplingRawReady x
  · rw [if_pos h] at ht
    constructor
    · rintro ⟨ta,ha⟩
      exact ⟨h,of_decide_eq_true (encode_injective (ht.deterministic ha).1)⟩
    · rintro ⟨_,hr⟩
      exact ⟨t,by simpa only [hr,decide_true] using ht⟩
  · rw [if_neg h] at ht
    constructor
    · rintro ⟨ta,ha⟩
      cases encode_injective (ht.deterministic ha).1
    · rintro ⟨hr,_⟩
      exact (h hr).elim
end MIPRE.Introspection.AuxiliaryProgram
