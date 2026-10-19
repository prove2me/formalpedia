-- Prove2me | solution 1 for MIPRE.OracleSampler.core_runs_within
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T02:48:06.654217+00:00
-- url     : https://prove2.me/submissions/c9c764f0-2d6e-4baf-9c93-81017ee740c9

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/OracularSampler.lean (solution of MIPRE.OracleSampler.core_runs_within);
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
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Basic
import Mathlib.Data.List.OfFn
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Pi
import Mathlib.Logic.Denumerable
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Function.Iterate
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Tactic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_SAT_Circuit
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_CL_Closure
import Definitions.Def_MIPRE_Foundations_CL_Closure_B
import Definitions.Def_MIPRE_Foundations_CL_Sampler
import Definitions.Def_MIPRE_Foundations_Verifier
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Fold
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_OracularGame
import Definitions.Def_MIPRE_Foundations_Closeness
import Definitions.Def_MIPRE_Foundations_PerfectStrategy
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_Foundations_GameDouble
import Definitions.Def_MIPRE_Foundations_OracularSound
import Definitions.Def_MIPRE_Foundations_OpBound
import Definitions.Def_MIPRE_Foundations_StateDistance
import Definitions.Def_MIPRE_Foundations_POVMValue
import Definitions.Def_MIPRE_Foundations_CrossConsistency
import Definitions.Def_MIPRE_Foundations_PVM
import Definitions.Def_MIPRE_Foundations_Commutation
import Definitions.Def_MIPRE_Foundations_Dilation
import Definitions.Def_MIPRE_Foundations_LowDegree_SchwartzZippel
import Definitions.Def_MIPRE_Foundations_Sandwich
import Definitions.Def_MIPRE_Foundations_POVMMix
import Definitions.Def_MIPRE_Foundations_GameAdapt
import Definitions.Def_MIPRE_Foundations_RegisterReindex
import Definitions.Def_MIPRE_Foundations_OracularTensor
import Definitions.Def_MIPRE_Foundations_OracularComplete
import Definitions.Def_MIPRE_Foundations_CL_Embedding
import Definitions.Def_MIPRE_Foundations_CL_Graph
import Definitions.Def_MIPRE_Foundations_CL_Detyping
import Definitions.Def_MIPRE_Foundations_CL_DetypingLaw
import Definitions.Def_MIPRE_Foundations_SampledGame
import Definitions.Def_MIPRE_Foundations_CL_DetypingGame
import Definitions.Def_MIPRE_Foundations_GapCompression
import Definitions.Def_MIPRE_Foundations_Cost_Codable_B
import Definitions.Def_MIPRE_Foundations_Halting_Descriptions
import Definitions.Def_MIPRE_Foundations_OracularTyped
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
import Definitions.Def_MIPRE_Foundations_Repeat_Prims
import Definitions.Def_MIPRE_Foundations_Repeat_MapLoop
import Definitions.Def_MIPRE_Foundations_Repeat_Sampler
import Definitions.Def_MIPRE_Foundations_CL_Repeat
import Definitions.Def_MIPRE_Foundations_Repeat_Bits
import Definitions.Def_MIPRE_Foundations_VerifierValue
import Definitions.Def_MIPRE_Foundations_Pipeline_Budget
import Definitions.Def_MIPRE_Foundations_Pipeline_Repetition
import Definitions.Def_MIPRE_Foundations_Repeat_RepSampler
import Definitions.Def_MIPRE_Foundations_Repeat_Dom
import Definitions.Def_MIPRE_Foundations_Repeat_SamplerCost
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgQueries
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgSampler
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgCost
import Definitions.Def_MIPRE_Foundations_OracularSampler
import Theorems.Thm_MIPRE_OracleSampler_size_call_le

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
theorem routeOneCall_direct_cost (route : PolyTimeFun Data (Bool × Data))
    (p : Prog) (post : PolyTimeFun (Data × Data) Data) (x r : Data)
    (h : route x = (false, r)) :
    ∃ t ≤ route.timeBound.eval x.size + r.size + 4,
      (routeOneCall route p post).Runs x r t := by
  obtain ⟨t, ht, hr⟩ := route.computes x
  rw [h] at hr
  refine ⟨_, ?_, Eval.let_ hr
    (Eval.elim_cons (i := 0) (a := Data.nil) (b := r) (by simp [encode, Data.ofBool])
      (Eval.elim_nil (i := 0) (by simp) (Eval.var_of_get (i := 1) (by simp))))⟩
  simp only [esize_data] at ht
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

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.OracleSampler
open Cost Cost.PolyTimeFun
open OracleSampler CL
open Repeat
variable {ℓ : ℕ} (S : Sampler (ℓ + 1))
variable {ℓ : ℕ} (S : Sampler (ℓ + 1))
theorem _root_.solution (n : ℕ) {B k : ℕ} (hS : S.TimeBoundAt n B k) (d : Data) :
    ∃ r t, t ≤ coreCost (Data.cons (encode S.prog) (.cons (encode n) d)).size B k (d.size + 1) ∧
      core.Runs (.cons (encode S.prog) (.cons (encode n) d)) r t := by
  set x : Data := .cons (encode S.prog) (.cons (encode n) d) with hx
  have hRt := route.esize_apply_le x
  have hd1 : 1 ≤ d.size := Data.size_pos d
  cases h : route x with
  | mk call payload =>
    cases call with
    | false =>
      obtain ⟨t, ht, hr⟩ := Prog.routeOneCall_direct_cost route selfUniversal.univ post x payload h
      refine ⟨payload, t, ?_, hr⟩
      rw [h] at hRt
      simp only [esize_prod, esize_false, esize_data] at hRt ht
      simp only [coreCost]
      omega
    | true =>
      obtain ⟨q', rfl⟩ := route_call_shape _ _ _ _ h
      have hq := size_call_le _ _ _ _ h
      obtain ⟨r, tS, htS, hSr⟩ := hS q'
      obtain ⟨tU, htU, hU⟩ := selfUniversal.time_le S.prog _ r tS hSr
      obtain ⟨t, ht, hr⟩ := Prog.routeOneCall_indirect_cost route selfUniversal.closed post x _
        .nil r tU h hU
      refine ⟨_, t, ?_, hr⟩
      rw [h] at hRt
      simp only [esize_prod, esize_true, esize_data, Data.size_cons] at hRt ht
      have hr_le : r.size ≤ tU := hU.size_le
      -- the input sampler's time on the forwarded query, at degree `5k`
      have hX : 2 ≤ d.size + 1 := by omega
      have hpow : (q'.size + 1) ^ k ≤ (d.size + 1) ^ (5 * k) := by
        rw [pow_mul]
        refine Nat.pow_le_pow_left ?_ k
        have h16 : 16 ≤ (d.size + 1) ^ 4 := by
          calc 16 = 2 ^ 4 := rfl
            _ ≤ (d.size + 1) ^ 4 := Nat.pow_le_pow_left hX 4
        nlinarith
      have htS' : tS ≤ B * (d.size + 1) ^ (5 * k) := htS.trans (Nat.mul_le_mul_left B hpow)
      have hes : esize S.prog = (encode S.prog : Data).size := rfl
      have hsz : esize S.prog + (Data.cons (encode n) q').size + tS ≤
          x.size + route.timeBound.eval x.size + B * (d.size + 1) ^ (5 * k) := by
        simp only [Data.size_cons] at hRt ⊢
        omega
      have htU' := htU.trans (polynomial_eval_mono _ hsz)
      have hpost := polynomial_eval_mono post.timeBound
        (show Data.nil.size + r.size + 1 ≤ tU + 2 by simp only [Data.size_nil]; omega)
      have hpost2 := polynomial_eval_mono post.timeBound (show tU + 2 ≤
        selfUniversal.bound.eval (x.size + route.timeBound.eval x.size +
          B * (d.size + 1) ^ (5 * k)) + 2 by omega)
      simp only [coreCost]
      omega
end MIPRE.OracleSampler
