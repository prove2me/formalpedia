-- Prove2me | solution 1 for MIPRE.Introspection.DecisionPreparation.prog_runs
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T04:53:26.729981+00:00
-- url     : https://prove2.me/submissions/d0dafe21-5c3e-49d9-924e-23168b800c71

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/DecisionPreparation.lean (solution of MIPRE.Introspection.DecisionPreparation.prog_runs);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Computability.Primrec.List
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Finset.Image
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Basic
import Mathlib.Data.List.OfFn
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Pi
import Mathlib.Logic.Denumerable
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_CL_Register
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
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_Foundations_GameDouble
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
import Definitions.Def_MIPRE_Foundations_Introspection_PauliSamplerParams
import Definitions.Def_MIPRE_Foundations_Introspection_Clock
import Definitions.Def_MIPRE_Foundations_Introspection_ClockCost
import Definitions.Def_MIPRE_Foundations_Introspection_ClockSimulation
import Definitions.Def_MIPRE_Foundations_Introspection_ClockCompiler
import Definitions.Def_MIPRE_Foundations_Introspection_ClockSimulationCost
import Definitions.Def_MIPRE_Foundations_Introspection_SourceCompilerParamsCost
import Definitions.Def_MIPRE_Foundations_Introspection_PauliSamplerParamsCost
import Definitions.Def_MIPRE_Foundations_Introspection_SourceCompilerGuard
import Definitions.Def_MIPRE_Foundations_Introspection_ParserGuard
import Definitions.Def_MIPRE_Foundations_Introspection_SourceCompiler
import Definitions.Def_MIPRE_Foundations_Introspection_SourceCompilerCost
import Definitions.Def_MIPRE_Foundations_Introspection_DecisionPreparation
import Theorems.Thm_MIPRE_Cost_Prog_routeOneCall_closed
import Theorems.Thm_MIPRE_Cost_Prog_routeOneCall_indirect
import Theorems.Thm_MIPRE_Introspection_ClockArithmetic_uniformProg_closed
import Theorems.Thm_MIPRE_Introspection_ClockArithmetic_uniformProg_runs
import Theorems.Thm_MIPRE_Introspection_PauliSamplerParameters_prog_closed
import Theorems.Thm_MIPRE_Introspection_PauliSamplerParameters_prog_runs
import Theorems.Thm_MIPRE_Introspection_SourceCompiler_boundsProg_runs

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
open Polynomial
open Data
theorem mulProg_wellScoped : mulProg.WellScoped 1 := by
  simp [mulProg, WellScoped, mulBody, addProg, lenBody]
end
end MIPRE.Cost.Prog

namespace MIPRE.Introspection.ClockArithmetic
noncomputable section
open Cost Cost.Prog Polynomial
theorem bothUnary_closed : bothUnary.WellScoped 1 := by
  refine ⟨by omega, trivial, ?_⟩
  exact ⟨callVar_wellScoped (by omega) toUnaryProg_wellScoped,
    callVar_wellScoped (by omega) toUnaryProg_wellScoped, by simp [WellScoped]⟩
end
end MIPRE.Introspection.ClockArithmetic

namespace MIPRE.Introspection.SourceCompiler
noncomputable section
open Cost Cost.Prog Cost.PolyTimeFun CL.Detyping.Program Polynomial
theorem powerUnaryProg_closed : powerUnaryProg.WellScoped 1 :=
  ⟨expBitsProg_wellScoped, toUnaryProg_wellScoped.mono (by omega) _⟩
end
end MIPRE.Introspection.SourceCompiler

namespace MIPRE.Introspection.SourceCompiler
noncomputable section
open Cost Cost.Prog Cost.PolyTimeFun CL.Detyping.Program Polynomial
theorem boundsProg_closed (c : ℕ) : (boundsProg c).WellScoped 1 :=
  ⟨ClockArithmetic.bothUnary_closed, mulProg_wellScoped.mono (by omega) _,
    (parameterSeed c).closed.mono (by omega) _,
    (callWithContext_closed powerUnaryProg_closed parameterPost).mono (by omega) _,
    (callWithContext_closed expBitsProg_wellScoped boundsPost).mono (by omega) _⟩
end
end MIPRE.Introspection.SourceCompiler

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

namespace MIPRE.Introspection.DecisionPreparation
noncomputable section
open Cost Cost.Prog Cost.PolyTimeFun CL.Detyping.Program SourceCompiler
theorem appendStage_closed (arg : PolyTimeFun Data Data) {p : Prog} (hp : p.WellScoped 1) :
    (appendStage arg p).WellScoped 1 := routeOneCall_closed _ hp _
end
end MIPRE.Introspection.DecisionPreparation

namespace MIPRE.Introspection.DecisionPreparation
noncomputable section
open Cost Cost.Prog Cost.PolyTimeFun CL.Detyping.Program SourceCompiler
theorem appendStage_runs (arg : PolyTimeFun Data Data) {p : Prog} (hp : p.WellScoped 1)
    (x r : Data) (t : ℕ) (hr : p.Runs (arg x) r t) :
    ∃ time, (appendStage arg p).Runs x (.cons x r) time :=
  routeOneCall_indirect (appendRoute arg) hp treePair x (arg x) x r t rfl hr
end
end MIPRE.Introspection.DecisionPreparation

namespace MIPRE.Introspection.DecisionPreparation
noncomputable section
open Cost Cost.Prog Cost.PolyTimeFun CL.Detyping.Program SourceCompiler
theorem sequence_closed {p q : Prog} (hp : p.WellScoped 1) (hq : q.WellScoped 1) :
    (sequence p q).WellScoped 1 := ⟨hp, hq.mono (by omega) _⟩
end
end MIPRE.Introspection.DecisionPreparation

namespace MIPRE.Introspection.DecisionPreparation
noncomputable section
open Cost Cost.Prog Cost.PolyTimeFun CL.Detyping.Program SourceCompiler
theorem sequence_runs {p q : Prog} (hq : q.WellScoped 1) {x y z : Data} {s t : ℕ}
    (hp : p.Runs x y s) (hr : q.Runs y z t) : (sequence p q).Runs x z (s+t+1) :=
  Eval.let_ hp (Eval.append_of_wellScoped hr hq _)
end
end MIPRE.Introspection.DecisionPreparation

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Introspection.DecisionPreparation
open Cost Cost.Prog Cost.PolyTimeFun CL.Detyping.Program SourceCompiler
set_option backward.isDefEq.respectTransparency false in
theorem _root_.solution (c : ℕ) (z : Data) :
    ∃ time, (prog c).Runs z (encode (resources c z)) time := by
  obtain ⟨t₁, _, h₁⟩ := ClockArithmetic.uniformProg_runs 5 (inputLambda z) (inputIndex z)
  obtain ⟨s₁, hs₁⟩ := appendStage_runs parameterInput (ClockArithmetic.uniformProg_closed 5)
    z _ t₁ h₁
  obtain ⟨t₂, h₂⟩ := ClockSimulation.reindexProg_runs (inputRaw z)
  obtain ⟨s₂, hs₂⟩ := appendStage_runs (inputRaw.comp treeHead) ClockSimulation.reindexProg_closed
    (.cons z (.ofNat (ansBound 5 (inputLambda z) (inputIndex z)))) _ t₂ h₂
  obtain ⟨t₃, h₃⟩ := PauliSamplerParameters.prog_runs c (inputLambda z) (inputIndex z)
  obtain ⟨s₃, hs₃⟩ := appendStage_runs (parameterInput.comp (treeHead.comp treeHead))
    (PauliSamplerParameters.prog_closed c) (indexResult z) _ t₃ h₃
  obtain ⟨t₄, h₄⟩ := boundsProg_runs c (inputLambda z) (inputIndex z)
  obtain ⟨s₄, hs₄⟩ := appendStage_runs (parameterInput.comp (treeHead.comp (treeHead.comp treeHead)))
    (boundsProg_closed c) (pauliResult c z) _ t₄ h₄
  obtain ⟨s₅, _, hs₅⟩ := finish.computes (.cons (.cons (.cons (.cons z
    (.ofNat (ansBound 5 (inputLambda z) (inputIndex z)))) (ClockSimulation.reindexed (inputRaw z)))
      (encode (PauliSamplerParameters.parameters c (inputLambda z) (inputIndex z))))
        (encode (registerBits c (inputLambda z) (inputIndex z),
          originalBound (inputLambda z) (inputIndex z))))
  have hout : finish (.cons (.cons (.cons (.cons z
    (.ofNat (ansBound 5 (inputLambda z) (inputIndex z)))) (ClockSimulation.reindexed (inputRaw z)))
      (encode (PauliSamplerParameters.parameters c (inputLambda z) (inputIndex z))))
        (encode (registerBits c (inputLambda z) (inputIndex z),
          originalBound (inputLambda z) (inputIndex z)))) = encode (resources c z) := by
    simp [finish, origin, preparedClock, preparedIndex, preparedParameters,
      ClockSimulation.reindexed, inputIndex, resources, encode_prod, encode_unary]
  rw [hout] at hs₅
  exact ⟨_, sequence_runs (sequence_closed (appendStage_closed _ ClockSimulation.reindexProg_closed)
    (sequence_closed (appendStage_closed _ (PauliSamplerParameters.prog_closed c))
      (sequence_closed (appendStage_closed _ (boundsProg_closed c)) finish.closed))) hs₁
      (sequence_runs (sequence_closed (appendStage_closed _ (PauliSamplerParameters.prog_closed c))
        (sequence_closed (appendStage_closed _ (boundsProg_closed c)) finish.closed)) hs₂
        (sequence_runs (sequence_closed (appendStage_closed _ (boundsProg_closed c)) finish.closed) hs₃
          (sequence_runs finish.closed hs₄ hs₅)))⟩
end MIPRE.Introspection.DecisionPreparation
