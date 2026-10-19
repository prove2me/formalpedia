-- Prove2me | solution 1 for MIPRE.Introspection.PauliSamplerParameters.prog_runs_cost
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T04:48:41.433358+00:00
-- url     : https://prove2.me/submissions/8e763253-bd48-4f88-a550-318f5d276002

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/PauliSamplerParamsCost.lean (solution of MIPRE.Introspection.PauliSamplerParameters.prog_runs_cost);
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
import Theorems.Thm_MIPRE_Cost_Prog_mulLoop_runs
import Theorems.Thm_MIPRE_Introspection_ClockArithmetic_bothUnary_runs
import Theorems.Thm_MIPRE_Introspection_PauliSamplerParameters_registerPower_eq

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

namespace MIPRE.Cost.Prog
section
open Polynomial
open Data
/-- `mulProg` multiplies unary numerals. -/
theorem mulProg_runs (a b : ℕ) :
    ∃ t ≤ (b + 1) * ((a + 1) * (4 * a + 2 * (a * b) + 15) + 4 * a + 4 * (a * b) + 2 * b + 41) +
        2 * b + 10,
      mulProg.Runs (Data.cons (ofNat a) (ofNat b)) (ofNat (a * b)) t := by
  obtain ⟨t, ht, hrun⟩ := mulLoop_runs a b 0 [ofNat b, Data.cons (ofNat a) (ofNat b)] (a * b)
    (by omega)
  have hpre := Eval.cons (Eval.var_of_get (env := [ofNat a, ofNat b, Data.cons (ofNat a) (ofNat b)])
    (i := 1) (v := ofNat b) (by simp)) (Eval.nil [ofNat a, ofNat b, Data.cons (ofNat a) (ofNat b)])
  have hrun' : Eval (Data.cons (ofNat b) Data.nil :: [ofNat a, ofNat b, Data.cons (ofNat a) (ofNat b)])
      (.loop mulBody) (ofNat (a * b)) t := by simpa [ofNat] using hrun
  refine ⟨_, ?_, Eval.elim_cons (i := 0) (a := ofNat a) (b := ofNat b) (by simp)
    (Eval.let_ hpre hrun')⟩
  ((try simp only [MIPRE.Cost.Data.size_cons, MIPRE.Cost.Data.size_nil, MIPRE.Cost.Data.size_ofNat, MIPRE.Cost.encode_bool, MIPRE.Cost.Data.ofBool, MIPRE.Cost.encode_bitStr_nil, Bool.toNat_false, Bool.toNat_true]) <;> omega)
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

namespace MIPRE.Introspection.SourceCompiler
noncomputable section
open Cost Cost.Prog Cost.PolyTimeFun CL.Detyping.Program Polynomial
theorem clampLog_apply (u : Unary) : clampLog u = unary (max 2 u.length) := by
  by_cases h : 2 ≤ u.length
  · simp [clampLog, PolyTimeFun.ite_apply, h, unary_length]
  · simp [clampLog, PolyTimeFun.ite_apply, h, Nat.max_eq_left (by omega : u.length ≤ 2)]
end
end MIPRE.Introspection.SourceCompiler

namespace MIPRE.Introspection.SourceCompiler
noncomputable section
open Cost Cost.Prog Cost.PolyTimeFun CL.Detyping.Program Polynomial
theorem unarySize_apply (u : Unary) : unarySize u = unary u.length.size := by
  simp [unarySize, Nat.size_eq_bits_len]
end
end MIPRE.Introspection.SourceCompiler

namespace MIPRE.Introspection.SourceCompiler
noncomputable section
open Cost Cost.Prog Cost.PolyTimeFun CL.Detyping.Program Polynomial
theorem parameterSeed_apply (c : ℕ) (u : Unary) :
    parameterSeed c u = (unary ((c * max 2 u.length + 1).size - 1), u,
      unary (c * (max 2 u.length - 1).size + 1)) := by
  simp [parameterSeed, unarySize_apply, clampLog_apply, unary, List.tail_replicate]
end
end MIPRE.Introspection.SourceCompiler

namespace MIPRE.Introspection.SourceCompiler
noncomputable section
open Cost Cost.Prog Cost.PolyTimeFun CL.Detyping.Program Polynomial
theorem powerUnaryProg_closed : powerUnaryProg.WellScoped 1 :=
  ⟨expBitsProg_wellScoped, toUnaryProg_wellScoped.mono (by omega) _⟩
end
end MIPRE.Introspection.SourceCompiler

namespace MIPRE.Introspection.SourceCompiler
noncomputable section
open Cost Cost.Prog Cost.PolyTimeFun CL.Detyping.Program ClockArithmetic
theorem powerUnaryProg_runs_cost (j : ℕ) : ∃ t ≤ powerUnaryCost j,
    powerUnaryProg.Runs (.ofNat j) (.ofNat (2^j)) t := by
  obtain ⟨t,ht,hr⟩ := expBitsProg_runs j
  obtain ⟨s,hs,hsr⟩ := toUnaryProg_runs (2^j)
  refine ⟨_,?_,Eval.let_ hr (Eval.append_of_wellScoped hsr toUnaryProg_wellScoped _)⟩
  change t ≤ exponentBitsCost j at ht
  change s ≤ unaryCost (2^j) at hs
  exact Nat.add_le_add_right (Nat.add_le_add ht hs) 1
end
end MIPRE.Introspection.SourceCompiler

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Introspection.PauliSamplerParameters
open Cost Cost.Prog Cost.PolyTimeFun CL.Detyping.Program SourceCompiler ClockArithmetic
theorem _root_.solution (c lam n : ℕ) : ∃ time ≤ cost c lam n,
    (prog c).Runs (encode (lam, n)) (encode (parameters c lam n)) time := by
  obtain ⟨t₁, ht₁, h₁⟩ := bothUnary_runs lam n
  obtain ⟨t₂, ht₂, h₂⟩ := mulProg_runs lam n
  obtain ⟨t₃, ht₃, h₃⟩ := (parameterSeed c).computes (unary (lam * n))
  have hs : parameterSeed c (unary (lam * n)) =
      (unary (selectorBits c lam n), unary (lam * n), unary (fieldBits c lam n)) := by
    simp only [parameterSeed_apply, length_unary, canonicalLog, selectorBits, fieldBits]
  rw [hs] at h₃
  obtain ⟨t₄, ht₄, h₄⟩ := powerInput.computes
    (unary (selectorBits c lam n), unary (lam * n), unary (fieldBits c lam n))
  have hi : powerInput (unary (selectorBits c lam n), unary (lam * n),
      unary (fieldBits c lam n)) =
      .cons (.ofNat (selectorBits c lam n))
        (.cons (.ofNat (fieldBits c lam n)) (.ofNat (selectorBits c lam n))) := by
    simp [powerInput, encode_unary]
  rw [hi] at h₄
  obtain ⟨t₅, ht₅, h₅⟩ := powerUnaryProg_runs_cost (selectorBits c lam n)
  obtain ⟨t₆, ht₆, h₆⟩ := callWithContext_cost powerUnaryProg_closed powerPost _
    (.cons (.ofNat (fieldBits c lam n)) (.ofNat (selectorBits c lam n))) _ t₅ h₅
  have ho : powerPost
      (.cons (.ofNat (fieldBits c lam n)) (.ofNat (selectorBits c lam n)),
        .ofNat (2 ^ selectorBits c lam n)) = encode (parameters c lam n) := by
    simp [powerPost, parameters, encode_prod, encode_unary, registerPower_eq]
  rw [ho] at h₆
  simp only [encode_unary] at h₃
  refine ⟨_, ?_, Eval.let_ h₁ (Eval.append_of_wellScoped (Eval.let_ h₂
    (Eval.append_of_wellScoped (Eval.let_ h₃ (Eval.append_of_wellScoped
      (Eval.let_ h₄ (Eval.append_of_wellScoped h₆
        (callWithContext_closed powerUnaryProg_closed powerPost) _))
      ⟨powerInput.closed, (callWithContext_closed powerUnaryProg_closed powerPost).mono
        (by omega) _⟩ _))
      ⟨(parameterSeed c).closed, powerInput.closed.mono (by omega) _,
        (callWithContext_closed powerUnaryProg_closed powerPost).mono (by omega) _⟩ _))
    ⟨mulProg_wellScoped, (parameterSeed c).closed.mono (by omega) _,
      powerInput.closed.mono (by omega) _,
      (callWithContext_closed powerUnaryProg_closed powerPost).mono (by omega) _⟩ _)⟩
  change t₂ ≤ mulCost lam n at ht₂
  simp only [esize_prod, esize_unary] at ht₃ ht₄
  have hm : 2 ^ selectorBits c lam n = registerPower c lam n := rfl
  rw [hm] at ht₆
  dsimp only [cost, contextCost]
  have harg : 2 * selectorBits c lam n + 1 +
      (2 * (lam * n) + 1 + (2 * fieldBits c lam n + 1) + 1) + 1 =
      2 * selectorBits c lam n + 2 * (lam * n) + 2 * fieldBits c lam n + 5 := by omega
  rw [harg] at ht₄
  omega
end MIPRE.Introspection.PauliSamplerParameters
