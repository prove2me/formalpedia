-- Prove2me | solution 1 for MIPRE.Introspection.SourceCompiler.boundsProg_runs
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T03:17:33.968249+00:00
-- url     : https://prove2.me/submissions/a44f5727-035d-4426-80aa-b94f36a36ff7

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/SourceCompilerParams.lean (solution of MIPRE.Introspection.SourceCompiler.boundsProg_runs);
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
import Theorems.Thm_MIPRE_Cost_Prog_mulLoop_runs
import Theorems.Thm_MIPRE_Introspection_ClockArithmetic_bothUnary_runs

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
open Cost Cost.Prog Cost.PolyTimeFun CL.Detyping.Program Polynomial
theorem powerUnaryProg_runs (j : ℕ) :
    ∃ t, powerUnaryProg.Runs (.ofNat j) (.ofNat (2 ^ j)) t := by
  obtain ⟨t, _, ht⟩ := expBitsProg_runs j
  obtain ⟨s, _, hs⟩ := toUnaryProg_runs (2 ^ j)
  exact ⟨_, Eval.let_ ht (Eval.append_of_wellScoped hs toUnaryProg_wellScoped _)⟩
end
end MIPRE.Introspection.SourceCompiler

namespace MIPRE.Introspection.SourceCompiler
noncomputable section
open Cost Cost.Prog Cost.PolyTimeFun CL.Detyping.Program Polynomial
theorem readUnary_ofNat (n : ℕ) : readUnary (.ofNat n) = unary n := by
  change unary (rawList (.ofNat n)).length = unary n
  congr 1
  induction n with
  | zero => rfl
  | succ n ih => simpa only [Data.ofNat, rawList, List.length_cons] using congrArg (· + 1) ih
end
end MIPRE.Introspection.SourceCompiler

namespace MIPRE.Introspection.SourceCompiler
noncomputable section
open Cost Cost.Prog Cost.PolyTimeFun CL.Detyping.Program Polynomial
theorem registerSizeProg_apply (m k : ℕ) :
    registerSizeProg (.cons (.ofNat m) (.ofNat k)) = 2 ^ m * k := by
  simp [registerSizeProg, readUnary_ofNat, unary, bitsVal_zeros, bitsVal_bits]
end
end MIPRE.Introspection.SourceCompiler

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Introspection.SourceCompiler
open Cost Cost.Prog Cost.PolyTimeFun CL.Detyping.Program Polynomial
theorem _root_.solution (c lam n : ℕ) : ∃ time,
    (boundsProg c).Runs (encode (lam, n)) (encode (registerBits c lam n, originalBound lam n)) time := by
  let j := (c * canonicalLog lam n + 1).size - 1
  let k := fieldBits c lam n
  let m := registerPower c lam n
  obtain ⟨t₁, _, h₁⟩ := ClockArithmetic.bothUnary_runs lam n
  obtain ⟨t₂, _, h₂⟩ := mulProg_runs lam n
  obtain ⟨t₃, _, h₃⟩ := (parameterSeed c).computes (unary (lam * n))
  have hs : parameterSeed c (unary (lam * n)) = (unary j, unary (lam * n), unary k) := by
    simp only [parameterSeed_apply, length_unary, canonicalLog, fieldBits, j, k]
  rw [hs] at h₃
  simp only [encode_prod, encode_unary] at h₃
  obtain ⟨t₄, h₄⟩ := powerUnaryProg_runs j
  obtain ⟨t₅, h₅⟩ := callWithContext_runs powerUnaryProg_closed parameterPost _
    (.cons (.ofNat (lam * n)) (.ofNat k)) _ t₄ h₄
  have h₅' : (callWithContext powerUnaryProg parameterPost).Runs
      (.cons (.ofNat j) (.cons (.ofNat (lam * n)) (.ofNat k)))
      (.cons (.ofNat (lam * n)) (.cons (.ofNat m) (.ofNat k))) t₅ := by
    simpa only [parameterPost, ap₂_apply, comp_apply, fst_apply, snd_apply, treeHead_cons,
      treeTail_cons, treePair_apply, m, registerPower, j] using h₅
  obtain ⟨t₆, _, h₆⟩ := expBitsProg_runs (lam * n)
  obtain ⟨t₇, h₇⟩ := callWithContext_runs expBitsProg_wellScoped boundsPost _
    (.cons (.ofNat m) (.ofNat k)) _ t₆ h₆
  have h₇' : (callWithContext expBitsProg boundsPost).Runs
      (.cons (.ofNat (lam * n)) (.cons (.ofNat m) (.ofNat k)))
      (encode (registerBits c lam n, originalBound lam n)) t₇ := by
    simpa only [boundsPost, ap₂_apply, comp_apply, fst_apply, snd_apply, encoded_apply,
      treePair_apply, registerSizeProg_apply, registerBits, originalBound, encode_prod, m, k] using h₇
  exact ⟨_, Eval.let_ h₁ (Eval.append_of_wellScoped (Eval.let_ h₂
    (Eval.append_of_wellScoped (Eval.let_ h₃ (Eval.append_of_wellScoped
      (Eval.let_ h₅' (Eval.append_of_wellScoped h₇'
        (callWithContext_closed expBitsProg_wellScoped boundsPost) _))
      ⟨callWithContext_closed powerUnaryProg_closed parameterPost,
        (callWithContext_closed expBitsProg_wellScoped boundsPost).mono (by omega) _⟩ _))
      ⟨(parameterSeed c).closed,
        (callWithContext_closed powerUnaryProg_closed parameterPost).mono (by omega) _,
        (callWithContext_closed expBitsProg_wellScoped boundsPost).mono (by omega) _⟩ _))
    ⟨mulProg_wellScoped, (parameterSeed c).closed.mono (by omega) _,
      (callWithContext_closed powerUnaryProg_closed parameterPost).mono (by omega) _,
      (callWithContext_closed expBitsProg_wellScoped boundsPost).mono (by omega) _⟩ _)⟩
end MIPRE.Introspection.SourceCompiler
