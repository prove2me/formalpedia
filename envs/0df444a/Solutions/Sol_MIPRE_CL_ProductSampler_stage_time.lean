-- Prove2me | solution 1 for MIPRE.CL.ProductSampler.stage_time
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T02:47:52.996034+00:00
-- url     : https://prove2.me/submissions/bf35bf84-2661-4eaf-be43-85b6224ef4c2

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/CL/ProductSamplerCost.lean (solution of MIPRE.CL.ProductSampler.stage_time);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Computability.Primrec.List
import Mathlib.Data.Finset.Image
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Basic
import Mathlib.Data.List.OfFn
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Pi
import Mathlib.Logic.Denumerable
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_SAT_Circuit
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_CL_Closure
import Definitions.Def_MIPRE_Foundations_CL_Closure_B
import Definitions.Def_MIPRE_Foundations_CL_Sampler
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Fold
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_CL_Embedding
import Definitions.Def_MIPRE_Foundations_CL_Graph
import Definitions.Def_MIPRE_Foundations_CL_Detyping
import Definitions.Def_MIPRE_Foundations_Cost_Codable_B
import Definitions.Def_MIPRE_Foundations_CL_Product
import Definitions.Def_MIPRE_Foundations_CL_Downsize
import Definitions.Def_MIPRE_Foundations_CL_TypedSampler
import Definitions.Def_MIPRE_Foundations_CL_ProductSampler
import Definitions.Def_MIPRE_Foundations_Cost_Binary
import Definitions.Def_MIPRE_Foundations_SAT_Formula
import Definitions.Def_MIPRE_Foundations_SAT_FmlLib
import Definitions.Def_MIPRE_Foundations_SAT_Flatten
import Definitions.Def_MIPRE_Foundations_Cost_Reader
import Definitions.Def_MIPRE_Foundations_SAT_FmlProg
import Definitions.Def_MIPRE_Foundations_SAT_ArrayProg
import Definitions.Def_MIPRE_Foundations_Cost_Iterates
import Definitions.Def_MIPRE_Foundations_LowDegree_UnaryDegreeArithmetic
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
import Definitions.Def_MIPRE_Foundations_CL_ProductSamplerProg
import Definitions.Def_MIPRE_Foundations_Cost_Growth
import Definitions.Def_MIPRE_Foundations_Repeat_Dom
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgQueries
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgSampler
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgCost
import Definitions.Def_MIPRE_Foundations_Cost_While
import Definitions.Def_MIPRE_Foundations_Pipeline_UnaryArith
import Definitions.Def_MIPRE_Foundations_Pipeline_PowDom
import Definitions.Def_MIPRE_Foundations_Pipeline_PowDomRun
import Definitions.Def_MIPRE_Foundations_CL_ProductSamplerCost
import Theorems.Thm_MIPRE_CL_ProductSampler_route_call_size

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
namespace MIPRE.CL.ProductSampler
open Cost Cost.PolyTimeFun CL.Detyping.Program Pipeline
variable (B : PolyTimeFun DirectInput BitStr) (D : PolyTimeFun Data Unary)
theorem _root_.solution (ap pp : Prog) (ℓa n : ℕ) (pdn q : Data) (BA k : ℕ)
    (hA : ∀ d, HaltsWithin ap (.cons (encode n) d) (BA * (d.size + 1) ^ k)) :
    ∃ r t, t ≤ stageBound B D ap ℓa n
        (Data.cons pdn (.cons (encode (ap, ℓa, pp)) (.cons (encode n) q))).size q.size BA k ∧
      (stage B D).Runs (.cons pdn (.cons (encode (ap, ℓa, pp)) (.cons (encode n) q))) r t := by
  set x : Data := .cons pdn (.cons (encode (ap, ℓa, pp)) (.cons (encode n) q)) with hx
  have hRt := (route B D).esize_apply_le x
  simp only [esize_data] at hRt
  cases h : route B D x with
  | mk call payload =>
    cases call with
    | false =>
      obtain ⟨t, ht, hr⟩ := Prog.routeOneCall_direct_cost (route B D) selfUniversal.univ post x
        payload h
      refine ⟨payload, t, ?_, hr⟩
      rw [h] at hRt
      simp only [esize_prod, esize_false, esize_data] at hRt ht
      simp only [stageBound]
      omega
    | true =>
      obtain ⟨a, ctx, rfl, ha⟩ := route_call_size B D ap pp ℓa n pdn q _ h
      obtain ⟨d, ctx', hshape⟩ := route_call_shape B D pdn (encode (ap, ℓa, pp)) (encode n) q _ h
      simp only [treeHead, encode_prod] at hshape
      have hshape' := Data.cons.inj hshape
      obtain ⟨hl, rfl⟩ := hshape'
      obtain ⟨_, rfl⟩ := Data.cons.inj hl
      obtain ⟨r, tA, htA, hArun⟩ := hA d
      obtain ⟨tU, htU, hU⟩ := selfUniversal.time_le ap _ r tA hArun
      obtain ⟨t, ht, hr⟩ := Prog.routeOneCall_indirect_cost (route B D) selfUniversal.closed post
        x _ ctx r tU h hU
      refine ⟨_, t, ?_, hr⟩
      rw [h] at hRt
      simp only [esize_prod, esize_true, esize_data, Data.size_cons] at hRt ht ha
      have e1 : (encode ap : Data).size = esize ap := rfl
      have e2 : (encode n : Data).size = esize n := rfl
      have hd : d.size + 1 ≤ esize n + 12 * q.size + 4 * ℓa + 21 := by omega
      have htA' : tA ≤ BA * (esize n + 12 * q.size + 4 * ℓa + 21) ^ k :=
        htA.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hd k))
      have hrs : r.size ≤ tU := hU.size_le
      have htU' := htU.trans (polynomial_eval_mono selfUniversal.bound (show esize ap +
        (Data.cons (encode n) d).size + tA ≤ esize ap + (esize n + 12 * q.size + 4 * ℓa + 20) +
          BA * (esize n + 12 * q.size + 4 * ℓa + 21) ^ k by
        simp only [Data.size_cons]; omega))
      have hpost := polynomial_eval_mono post.timeBound
        (show ctx.size + r.size + 1 ≤ (route B D).timeBound.eval x.size +
          selfUniversal.bound.eval (esize ap + (esize n + 12 * q.size + 4 * ℓa + 20) +
            BA * (esize n + 12 * q.size + 4 * ℓa + 21) ^ k) + 1 by omega)
      simp only [stageBound]
      omega
end MIPRE.CL.ProductSampler
