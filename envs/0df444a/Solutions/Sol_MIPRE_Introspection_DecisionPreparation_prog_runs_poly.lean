-- Prove2me | solution 1 for MIPRE.Introspection.DecisionPreparation.prog_runs_poly
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T05:47:54.676275+00:00
-- url     : https://prove2.me/submissions/3476fcff-d1d9-40db-9664-90f315908768

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/DecisionPreparationCost.lean (solution of MIPRE.Introspection.DecisionPreparation.prog_runs_poly);
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
import Definitions.Def_MIPRE_Foundations_Introspection_DecisionPreparationCost
import Theorems.Thm_MIPRE_Cost_Prog_routeOneCall_closed
import Theorems.Thm_MIPRE_Introspection_ClockArithmetic_growingClock_cost_le
import Theorems.Thm_MIPRE_Introspection_ClockArithmetic_uniformProg_closed
import Theorems.Thm_MIPRE_Introspection_ClockArithmetic_uniformProg_runs
import Theorems.Thm_MIPRE_Introspection_ClockSimulation_reindexCost_le
import Theorems.Thm_MIPRE_Introspection_ClockSimulation_reindexProg_runs_cost
import Theorems.Thm_MIPRE_Introspection_DecisionPreparation_boundsCost_le_majorant
import Theorems.Thm_MIPRE_Introspection_PauliSamplerParameters_costMajorant_polyBounded
import Theorems.Thm_MIPRE_Introspection_PauliSamplerParameters_cost_le_majorant
import Theorems.Thm_MIPRE_Introspection_PauliSamplerParameters_prog_closed
import Theorems.Thm_MIPRE_Introspection_PauliSamplerParameters_prog_runs_cost
import Theorems.Thm_MIPRE_Introspection_SourceCompiler_boundsProg_runs_cost

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

namespace MIPRE.Cost.Machine
section
open Prog
theorem size_right_le (d : Data) : d.right.size ≤ d.size := by cases d <;> simp; omega
end
end MIPRE.Cost.Machine

namespace MIPRE.Cost.Prog
section
open Polynomial
open Data
theorem mulProg_wellScoped : mulProg.WellScoped 1 := by
  simp [mulProg, WellScoped, mulBody, addProg, lenBody]
end
end MIPRE.Cost.Prog

namespace MIPRE.Cost.Prog
section
open PolyTimeFun Polynomial
theorem callWithContext_cost {p : Prog} (hp : p.WellScoped 1)
    (post : PolyTimeFun (Data × Data) Data) (a ctx r : Data) (time : ℕ)
    (hr : p.Runs a r time) :
    ∃ t ≤ 2 * a.size + 2 * ctx.size + r.size + time +
        post.timeBound.eval (ctx.size + r.size + 1) + 12,
      (callWithContext p post).Runs (.cons a ctx) (post (ctx, r)) t := by
  obtain ⟨tp, htp, hpRun⟩ := post.computes (ctx, r)
  have ectx := callVar_eval (env := [r, a, Data.cons a ctx]) (i := 2)
    sndProg_wellScoped (by simp) (sndProg_runs a ctx)
  have run := Eval.let_ (fstProg_runs a ctx)
    (Eval.let_ (Eval.append_of_wellScoped hr hp _)
      (Eval.let_ (Eval.cons ectx (Eval.var_of_get (i := 0) (by simp)))
        (Eval.append_of_wellScoped hpRun post.closed _)))
  refine ⟨_, ?_, run⟩
  simp only [esize_prod, esize_data, Data.size_cons, encode_data] at *
  omega
end
end MIPRE.Cost.Prog

namespace MIPRE.Cost.Prog
section
open PolyTimeFun Polynomial
theorem routeOneCall_indirect_cost (route : PolyTimeFun Data (Bool × Data))
    {p : Prog} (hp : p.WellScoped 1) (post : PolyTimeFun (Data × Data) Data)
    (x a ctx r : Data) (time : ℕ) (h : route x = (true, .cons a ctx))
    (hr : p.Runs a r time) :
    ∃ t ≤ route.timeBound.eval x.size + 3 * a.size + 3 * ctx.size + r.size + time +
        post.timeBound.eval (ctx.size + r.size + 1) + 18,
      (routeOneCall route p post).Runs x (post (ctx, r)) t := by
  obtain ⟨t, ht, hroute⟩ := route.computes x
  rw [h] at hroute
  obtain ⟨tc, htc, hc⟩ := callWithContext_cost hp post a ctx r time hr
  refine ⟨_, ?_, Eval.let_ hroute
    (Eval.elim_cons (i := 0) (a := Data.cons .nil .nil) (b := .cons a ctx)
      (by simp [encode, Data.ofBool])
      (Eval.elim_cons (i := 0) (a := Data.nil) (b := .nil) (by simp)
        (callVar_eval (i := 3) (callWithContext_closed hp post) (by simp) hc)))⟩
  simp only [esize_data, Data.size_cons] at *
  omega
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

namespace MIPRE.Introspection.ClockArithmetic
noncomputable section
open Cost Polynomial
theorem clock_arguments_le {k lam n : ℕ} (hk : 1 ≤ k) (hl : 1 ≤ lam) (hn : 1 ≤ n) :
    lam ≤ ansBound k lam n ∧ n ≤ ansBound k lam n ∧
      lam * n + 1 ≤ ansBound k lam n ∧ (lam * n + 1) ^ k ≤ ansBound k lam n := by
  have hm : lam * n + 1 ≤ (lam * n + 1) ^ k := by
    simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 1 ≤ lam * n + 1) hk
  have hq : (lam * n + 1) ^ k ≤ ansBound k lam n := Nat.lt_two_pow_self.le
  have hlam : lam ≤ lam * n := by simpa only [Nat.mul_one] using Nat.mul_le_mul_left lam hn
  have hnn : n ≤ lam * n := by simpa only [Nat.one_mul] using Nat.mul_le_mul_right n hl
  exact ⟨(by omega : lam ≤ lam * n + 1).trans (hm.trans hq),
    (by omega : n ≤ lam * n + 1).trans (hm.trans hq), hm.trans hq, hq⟩
end
end MIPRE.Introspection.ClockArithmetic

namespace MIPRE.Introspection.ClockSimulation
noncomputable section
open Cost Cost.Prog Cost.PolyTimeFun CL.Detyping CL.Detyping.Program
theorem reindexProg_closed : reindexProg.WellScoped 1 :=
  ⟨indexReader.closed, toUnaryProg_wellScoped.mono (by omega) _,
    expBitsProg_wellScoped.mono (by omega) _, by simp [WellScoped],
    callVar_wellScoped (by omega) treeTail.closed⟩
end
end MIPRE.Introspection.ClockSimulation

namespace MIPRE.Introspection.SourceCompiler
noncomputable section
open Cost Cost.Prog Cost.PolyTimeFun CL.Detyping CL.Detyping.Program
theorem call_runs_cost (route : PolyTimeFun Data (Bool × Data))
    (post : PolyTimeFun (Data × Data) Data) {p : Prog} (hp : p.WellScoped 1)
    (x a ctx r : Data) (T t : ℕ) (ht : t ≤ T)
    (hroute : route x = (true,.cons a ctx)) (hr : p.Runs a r t) :
    ∃ time ≤ callCost route post x a ctx T,
      (routeOneCall route p post).Runs x (post (ctx,r)) time := by
  obtain ⟨time,hb,hh⟩ := routeOneCall_indirect_cost route hp post x a ctx r t hroute hr
  have hs : r.size ≤ T := hr.size_le.trans ht
  have hm := polynomial_eval_mono post.timeBound (Nat.add_le_add_right (Nat.add_le_add_left hs ctx.size) 1)
  refine ⟨time,hb.trans ?_,hh⟩
  dsimp only [callCost]
  omega
end
end MIPRE.Introspection.SourceCompiler

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

namespace MIPRE.Introspection.DecisionPreparation
noncomputable section
open Cost Cost.Prog Cost.PolyTimeFun CL.Detyping.Program SourceCompiler Polynomial
theorem esize_two_pow_le (n : ℕ) : esize (2 ^ n) ≤ 4 * n + 5 := by
  have h := esize_nat_le (2 ^ n)
  rw [Nat.size_pow] at h
  omega
end
end MIPRE.Introspection.DecisionPreparation

namespace MIPRE.Introspection.DecisionPreparation
noncomputable section
open Cost Cost.Prog Cost.PolyTimeFun CL.Detyping.Program SourceCompiler Polynomial
theorem appendStage_runs_poly (arg : PolyTimeFun Data Data) {code : Prog}
    (hcode : code.WellScoped 1) (p q : Polynomial ℕ) (v : ℕ) (x r : Data)
    (hx : x.size ≤ p.eval v) (t : ℕ) (ht : t ≤ q.eval v) (hr : code.Runs (arg x) r t) :
    ∃ time ≤ (appendPoly arg p q).eval v,
      (appendStage arg code).Runs x (.cons x r) time := by
  obtain ⟨s, hs, hout⟩ := call_runs_cost (appendRoute arg) treePair hcode x (arg x) x r
    (q.eval v) t ht rfl hr
  have harg := arg.esize_apply_le x
  have hmarg := polynomial_eval_mono arg.timeBound hx
  have hmroute := polynomial_eval_mono (appendRoute arg).timeBound hx
  have hmpost := polynomial_eval_mono treePair.timeBound
    (Nat.add_le_add_right (Nat.add_le_add_right hx (q.eval v)) 1)
  refine ⟨s, hs.trans ?_, hout⟩
  simp only [appendPoly, eval_add, eval_mul, eval_comp, eval_ofNat, eval_one]
  change (arg x).size ≤ arg.timeBound.eval x.size at harg
  dsimp only [callCost]
  omega
end
end MIPRE.Introspection.DecisionPreparation

namespace MIPRE.Introspection.DecisionPreparation
noncomputable section
open Cost Cost.Prog Cost.PolyTimeFun CL.Detyping.Program SourceCompiler Polynomial
theorem finish_boundsResult (c : ℕ) (z : Data) :
    finish (boundsResult c z) = encode (resources c z) := by
  simp [boundsResult, pauliResult, indexResult, clockResult, finish, origin,
    preparedClock, preparedIndex, preparedParameters, ClockSimulation.reindexed,
    inputIndex, resources, encode_prod, encode_unary]
end
end MIPRE.Introspection.DecisionPreparation

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Introspection.DecisionPreparation
open Cost Cost.Prog Cost.PolyTimeFun CL.Detyping.Program SourceCompiler Polynomial
set_option backward.isDefEq.respectTransparency false in
theorem _root_.solution {c v : ℕ} (hc : 1 ≤ c) (z : Data)
    (hl : 1 ≤ inputLambda z) (hn : 1 ≤ inputIndex z)
    (hz : z.size ≤ v) (hB : ansBound 5 (inputLambda z) (inputIndex z) ≤ v) :
    ∃ time ≤ (preparationPoly c).eval v,
      (prog c).Runs z (encode (resources c z)) time := by
  obtain ⟨hlB, hnB, huB, _⟩ := ClockArithmetic.clock_arguments_le (by decide : 1 ≤ 5) hl hn
  have hlv := hlB.trans hB
  have hnv := hnB.trans hB
  have huv : inputLambda z * inputIndex z ≤ v := by omega
  have hv : 1 ≤ v := hl.trans hlv
  obtain ⟨t₁, ht₁, h₁⟩ := ClockArithmetic.uniformProg_runs 5 (inputLambda z) (inputIndex z)
  have hc₁ := ClockArithmetic.growingClock_cost_le (by decide : 1 ≤ 5) hl hn
  have hc₂ := polynomial_eval_mono (ClockArithmetic.clockCostPoly 5) hB
  have htc : t₁ ≤ clockPoly.eval v := by unfold clockPoly; omega
  obtain ⟨s₁, hts₁, hs₁⟩ := appendStage_runs_poly parameterInput
    (ClockArithmetic.uniformProg_closed 5) X clockPoly v z _
      (by simpa using hz) t₁ htc h₁
  change (clockStage).Runs z (clockResult z) s₁ at hs₁
  change s₁ ≤ firstPoly.eval v at hts₁
  have hz₁ : (clockResult z).size ≤ firstPoly.eval v := hs₁.size_le.trans hts₁
  have hx : (inputRaw z).size ≤ v := (Machine.size_right_le z).trans hz
  have htail : (treeTail (inputRaw z)).size ≤ v :=
    (Machine.size_right_le (inputRaw z)).trans hx
  have hpow := esize_two_pow_le (inputIndex z)
  have hout : (ClockSimulation.reindexed (inputRaw z)).size ≤ 64*v := by
    change esize (2^inputIndex z) + (treeTail (inputRaw z)).size + 1 ≤ 64*v
    omega
  obtain ⟨t₂, ht₂, h₂⟩ := ClockSimulation.reindexProg_runs_cost (inputRaw z)
  have hri := ClockSimulation.reindexCost_le hnv (show (inputRaw z).size ≤ 64*v by omega) hout
  obtain ⟨s₂, hts₂, hs₂⟩ := appendStage_runs_poly (inputRaw.comp treeHead)
    ClockSimulation.reindexProg_closed firstPoly ClockSimulation.reindexCostPoly v
    (clockResult z) _ hz₁ t₂ (ht₂.trans hri) h₂
  change indexStage.Runs (clockResult z) (indexResult z) s₂ at hs₂
  have hz₂ : (indexResult z).size ≤ secondPoly.eval v := by
    have := hs₂.size_le
    simp only [secondPoly, eval_add, eval_one]
    omega
  obtain ⟨t₃, ht₃, h₃⟩ := PauliSamplerParameters.prog_runs_cost c (inputLambda z) (inputIndex z)
  have hp₃ := PauliSamplerParameters.cost_le_majorant hc hlv hnv huv
  have hq₃ := (PauliSamplerParameters.costMajorant_polyBounded c).le_poly_eval v
  obtain ⟨s₃, hts₃, hs₃⟩ := appendStage_runs_poly
    (parameterInput.comp (treeHead.comp treeHead)) (PauliSamplerParameters.prog_closed c)
    secondPoly (pauliPoly c) v (indexResult z) _ hz₂ t₃ (ht₃.trans (hp₃.trans hq₃)) h₃
  change (pauliStage c).Runs (indexResult z) (pauliResult c z) s₃ at hs₃
  have hz₃ : (pauliResult c z).size ≤ (thirdPoly c).eval v := by
    have := hs₃.size_le
    simp only [thirdPoly, eval_add, eval_one]
    omega
  obtain ⟨t₄, ht₄, h₄⟩ := boundsProg_runs_cost c (inputLambda z) (inputIndex z)
  have hp₄ := boundsCost_le_majorant hc hlv hnv huv
  have hq₄ := (boundsMajorant_polyBounded c).le_poly_eval v
  obtain ⟨s₄, hts₄, hs₄⟩ := appendStage_runs_poly
    (parameterInput.comp (treeHead.comp (treeHead.comp treeHead))) (boundsProg_closed c)
    (thirdPoly c) (boundsPoly c) v (pauliResult c z) _ hz₃ t₄ (ht₄.trans (hp₄.trans hq₄)) h₄
  change (boundsStage c).Runs (pauliResult c z) (boundsResult c z) s₄ at hs₄
  have hz₄ : (boundsResult c z).size ≤ (fourthPoly c).eval v := by
    have := hs₄.size_le
    simp only [fourthPoly, eval_add, eval_one]
    omega
  obtain ⟨s₅, hts₅, hs₅⟩ := finish.computes (boundsResult c z)
  have hfin := polynomial_eval_mono finish.timeBound hz₄
  rw [finish_boundsResult] at hs₅
  refine ⟨_, ?_, sequence_runs
    (sequence_closed (appendStage_closed _ ClockSimulation.reindexProg_closed)
      (sequence_closed (appendStage_closed _ (PauliSamplerParameters.prog_closed c))
        (sequence_closed (appendStage_closed _ (boundsProg_closed c)) finish.closed))) hs₁
      (sequence_runs (sequence_closed (appendStage_closed _ (PauliSamplerParameters.prog_closed c))
        (sequence_closed (appendStage_closed _ (boundsProg_closed c)) finish.closed)) hs₂
        (sequence_runs (sequence_closed (appendStage_closed _ (boundsProg_closed c)) finish.closed) hs₃
          (sequence_runs finish.closed hs₄ hs₅)))⟩
  simp only [preparationPoly, fourthPoly, thirdPoly, secondPoly,
    eval_add, eval_one, eval_comp] at hts₂ hts₃ hts₄ hfin ⊢
  change s₅ ≤ finish.timeBound.eval (boundsResult c z).size at hts₅
  omega
end MIPRE.Introspection.DecisionPreparation
